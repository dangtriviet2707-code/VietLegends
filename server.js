'use strict';
// Mini MMORPG: server quyết định mọi thứ (di chuyển, đánh quái, EXP, vật phẩm, nhiệm vụ).
// Client chỉ gửi ý định (hướng đi, tấn công, dùng bình, mặc đồ...) và vẽ lại những gì server báo.
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = Number(process.env.PORT) || 3000;
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data'); // khi lên web: trỏ DATA_DIR vào ổ đĩa bền vững
const DB_FILE = path.join(DATA_DIR, 'accounts.json');
const TILE = 32;
const TICK_MS = 50;
const MAX_LEVEL = 30;
const VIEW_RADIUS = 1000;
const BAG_CAP = 30;
const BASE_SPEED = 150;

// ---------------------------------------------------------------- lưu trữ
let db = {};
try { db = JSON.parse(fs.readFileSync(DB_FILE, 'utf8')); } catch (e) { db = {}; }
function saveDB() {
  fs.mkdirSync(DATA_DIR, { recursive: true });
  const tmp = DB_FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(db));
  fs.renameSync(tmp, DB_FILE);
}

// ---------------------------------------------------------------- cấp bậc
// [cấp bắt đầu, tên bậc]
const RANKS = [[1, 'Dân Thường'], [4, 'Chiến Binh'], [7, 'Chiến Binh Cao Cấp'], [11, 'Vệ Binh'],
  [16, 'Vệ Binh Cao Cấp'], [21, 'Vệ Binh Hoàng Gia'], [26, 'Mãnh Tướng']];
function rankOf(lv) { let r = RANKS[0][1]; for (const [m, n] of RANKS) if (lv >= m) r = n; return r; }
// Cấp càng cao càng cần nhiều EXP (cấp 1: 30, cấp 10: ~1500, cấp 29: ~9200)
const expNeed = lv => Math.floor(30 * Math.pow(lv, 1.7));

// ---------------------------------------------------------------- trang bị
const RARITIES = [
  { n: 'Thường', m: 1, sell: 1 },
  { n: 'Hiếm', m: 1.5, sell: 3 },
  { n: 'Thần Thoại', m: 2.4, sell: 9 }
];
const TIER_NAMES = ['Vải Thô', 'Da Thú', 'Sắt', 'Thép', 'Huyền Thiết', 'Thiên Kim'];
const TIER_SELL = [6, 14, 30, 55, 90, 140];
const SLOTS = {
  top: { label: 'Áo', hp: 30, def: 3, spd: 0 },
  bottom: { label: 'Quần', hp: 16, def: 2, spd: 0 },
  boots: { label: 'Giày', hp: 8, def: 1, spd: 5 }
};
const SLOT_KEYS = Object.keys(SLOTS);
// Vật phẩm lưu gọn {s: ô, r: độ hiếm 0-2, t: bậc chất liệu 0-5}; chỉ số tính từ 3 giá trị này.
function cleanItem(it) {
  if (!it || !SLOTS[it.s]) return null;
  const r = Number(it.r), t = Number(it.t);
  if (!(r >= 0 && r <= 2 && t >= 0 && t <= 5)) return null;
  return { s: it.s, r: r | 0, t: t | 0 };
}
function itemView(it) {
  const sl = SLOTS[it.s], tm = 1 + it.t * 0.9, rm = RARITIES[it.r].m;
  return {
    s: it.s, r: it.r, t: it.t, name: sl.label + ' ' + TIER_NAMES[it.t], rn: RARITIES[it.r].n, sl: sl.label,
    hp: Math.round(sl.hp * tm * rm), def: Math.round(sl.def * tm * rm),
    spd: sl.spd ? Math.round(sl.spd * rm * (1 + it.t * 0.15)) : 0,
    atk: it.r === 2 ? Math.round(3 * tm) : 0,
    price: Math.round(TIER_SELL[it.t] * RARITIES[it.r].sell)
  };
}
const itemTitle = it => { const v = itemView(it); return v.name + ' [' + v.rn + ']'; };
function gearTotals(p) {
  const g = { hp: 0, def: 0, spd: 0, atk: 0 };
  for (const s of SLOT_KEYS) {
    if (!p.eq[s]) continue;
    const v = itemView(p.eq[s]);
    g.hp += v.hp; g.def += v.def; g.spd += v.spd; g.atk += v.atk;
  }
  g.spd = Math.min(g.spd, 40);
  return g;
}
function rollRarity(boss) {
  const x = Math.random();
  if (boss) return x < 0.25 ? 2 : 1;           // boss: chắc chắn Hiếm trở lên
  return x < 0.015 ? 2 : (x < 0.18 ? 1 : 0);   // quái thường: 82% / 16.5% / 1.5%
}
function rollGear(tier, boss) {
  return { s: SLOT_KEYS[Math.floor(Math.random() * SLOT_KEYS.length)], r: rollRarity(boss), t: Math.max(0, Math.min(5, tier)) };
}

// ---------------------------------------------------------------- bản đồ
// Ký tự: . cỏ/nền  = đường  # cây/vật cản  ~ nước/dung nham  P cổng dịch chuyển
function rng(seed) {
  let s = seed >>> 0;
  return () => { s = (Math.imul(s, 1664525) + 1013904223) >>> 0; return s / 4294967296; };
}
function buildMap(def) {
  const r = rng(def.seed);
  const g = [];
  for (let y = 0; y < def.h; y++) {
    const row = [];
    for (let x = 0; x < def.w; x++) {
      const edge = x === 0 || y === 0 || x === def.w - 1 || y === def.h - 1;
      let c = '.';
      if (edge) c = '#';
      else if (r() < def.trees) c = '#';
      row.push(c);
    }
    g.push(row);
  }
  for (let i = 0; i < def.ponds; i++) {
    const pw = 3 + Math.floor(r() * 4), ph = 2 + Math.floor(r() * 3);
    const px = 3 + Math.floor(r() * (def.w - pw - 6)), py = 3 + Math.floor(r() * (def.h - ph - 6));
    for (let y = py; y < py + ph; y++) for (let x = px; x < px + pw; x++) g[y][x] = '~';
  }
  const midY = Math.floor(def.h / 2);
  for (let x = 1; x < def.w - 1; x++) for (let y = midY - 1; y <= midY + 1; y++) g[y][x] = '=';
  const clear = (cx, cy, rad) => {
    for (let y = cy - rad; y <= cy + rad; y++) for (let x = cx - rad; x <= cx + rad; x++)
      if (x > 0 && y > 0 && x < def.w - 1 && y < def.h - 1 && g[y][x] !== '=') g[y][x] = '.';
  };
  for (const p of (def.portals || [])) {
    clear(p.x < def.w / 2 ? 2 : def.w - 3, midY, 2);
    const px = p.x < def.w / 2 ? 0 : def.w - 1;
    for (let y = midY - 1; y <= midY + 1; y++) g[y][px] = 'P';
  }
  if (def.spawnArea) clear(def.spawnArea.x, def.spawnArea.y, 3);
  if (def.shop) clear(def.shop.x, def.shop.y, 1);
  if (def.npc) clear(def.npc.x, def.npc.y, 1);
  for (const t of (def.teachers || [])) clear(t.x, t.y, 1);
  if (def.cage) clear(def.cage.x, def.cage.y, 2);
  for (const f of def.fixed || []) clear(f.x, f.y, 2);
  return { ...def, rows: g.map(row => row.join('')), grid: g, midY };
}

// Điều kiện vào map (xem GATES bên dưới). Đổi luật mở khóa chỉ cần sửa ở đây.
const MAP_DEFS = {
  // ===== DÂN GIAN =====
  town: {
    id: 'town', name: 'Làng Khởi Đầu', realm: 'Dân Gian', theme: 'folk', w: 32, h: 22, seed: 11, trees: 0.04, ponds: 1, safe: true,
    spawn: { x: 16, y: 11 }, spawnArea: { x: 16, y: 11 },
    portals: [{ x: 31, to: 'field', tx: 3, ty: null }],
    mobs: [], shop: { x: 12, y: 8 }, npc: { x: 20, y: 9, name: 'Trưởng Làng Mộc' }
  },
  field: {
    id: 'field', name: 'Đồng Cỏ Xanh', realm: 'Dân Gian', theme: 'folk', w: 52, h: 34, seed: 23, trees: 0.06, ponds: 3, safe: false,
    portals: [{ x: 0, to: 'town', tx: 28, ty: null }, { x: 51, to: 'forest', tx: 3, ty: null }],
    mobs: [{ tpl: 'slime', n: 14 }, { tpl: 'boar', n: 8 }, { tpl: 'dino', n: 5 }],
    npc: { x: 6, y: 13, name: 'Thợ Săn Bảy' }
  },
  forest: {
    id: 'forest', name: 'Rừng Sương Mù', realm: 'Dân Gian', theme: 'folk', w: 60, h: 38, seed: 37, trees: 0.12, ponds: 4, safe: false,
    enter: 'q1',
    portals: [{ x: 0, to: 'field', tx: 48, ty: null }, { x: 59, to: 'duong', tx: 3, ty: null }],
    mobs: [{ tpl: 'phi', n: 12 }, { tpl: 'wolf', n: 6 }, { tpl: 'ent', n: 4 }],
    road: [{ tpl: 'wolf', n: 5 }, { tpl: 'ent', n: 2 }, { tpl: 'phi', n: 4 }],      // quái đứng chặn trên đường
    fixed: [{ tpl: 'bwolf', x: 20, y: 19 }, { tpl: 'bent', x: 32, y: 19 }, { tpl: 'bking', x: 45, y: 19 }], // boss chặn đường
    cage: { x: 53, y: 19 },                                                          // lồng giam công chúa ở cuối map
    npc: { x: 6, y: 15, name: 'Lính Canh Sống Sót' }
  },
  // ===== ĐẠI LỘ ÂM DƯƠNG =====
  duong: {
    id: 'duong', name: 'Đại Lộ Âm Dương', realm: 'Cửa Âm Dương', theme: 'hell', w: 58, h: 36, seed: 45, trees: 0.08, ponds: 3, safe: false, enter: 'road16',
    portals: [{ x: 0, to: 'forest', tx: 55, ty: null }, { x: 57, to: 'am', tx: 3, ty: null }],
    mobs: [{ tpl: 'ghost', n: 12 }, { tpl: 'quysai', n: 8 }], road: [{ tpl: 'quysai', n: 5 }],
    fixed: [{ tpl: 'broad', x: 46, y: 18 }], npc: { x: 6, y: 15, name: 'Lý Bạch' },
    teachers: [{ id: 'palm', x: 11, y: 22, name: 'Ma Đạo Sư' }]
  },
  // ===== ÂM GIỚI =====
  am: {
    id: 'am', name: 'Hoang Mạc Hồn', realm: 'Âm Giới', theme: 'hell', w: 62, h: 40, seed: 51, trees: 0.10, ponds: 5, safe: false, enter: 'pass',
    portals: [{ x: 0, to: 'duong', tx: 53, ty: null }, { x: 61, to: 'daidien', tx: 3, ty: null }],
    mobs: [{ tpl: 'vonglinh', n: 14 }, { tpl: 'quysai', n: 8 }, { tpl: 'skeleton', n: 10 }, { tpl: 'demon', n: 6 }],
    road: [{ tpl: 'vonglinh', n: 4 }, { tpl: 'quysai', n: 4 }, { tpl: 'skeleton', n: 4 }],
    fixed: [{ tpl: 'chungquy', x: 50, y: 20 }], npc: { x: 6, y: 16, name: 'Lý Bạch' }
  },
  daidien: {
    id: 'daidien', name: 'Đại Điện U Minh', realm: 'Âm Giới', theme: 'hell', w: 48, h: 32, seed: 61, trees: 0.02, ponds: 0, safe: false, enter: 'palace',
    portals: [{ x: 0, to: 'am', tx: 58, ty: null }, { x: 47, to: 'sky', tx: 3, ty: null }], mobs: [{ tpl: 'quigac', n: 12 }], road: [{ tpl: 'quigac', n: 4 }],
    fixed: [], npc: { x: 7, y: 15, name: 'Lý Bạch' }
  },
  // Phòng nghi lễ riêng: chỉ có Hắc Vô Thường và Bạch Vô Thường, tuyệt đối không sinh quái/cổng.
  hbdien: {
    id: 'hbdien', name: 'Điện Dẫn Hồn', realm: 'Âm Giới', theme: 'hell', w: 30, h: 20, seed: 89, trees: 0, ponds: 0, safe: true,
    spawn: { x: 15, y: 14 }, spawnArea: { x: 15, y: 14 }, portals: [], mobs: [], road: [], fixed: [],
    npc: { x: 15, y: 9, name: 'Hắc Bạch Vô Thường' }
  },
  // ===== THIÊN GIỚI =====
  sky: {
    id: 'sky', name: 'Nam Thiên Môn', realm: 'Thiên Giới', theme: 'heaven', w: 64, h: 42, seed: 77, trees: 0.04, ponds: 2, safe: false,
    enter: 'skyStart', portals: [{ x: 0, to: 'daidien', tx: 44, ty: null }, { x: 63, to: 'sky_peach', tx: 3, ty: null }],
    mobs: [{ tpl: 'thienbinh', n: 14 }], road: [{ tpl: 'thienbinh', n: 5 }], fixed: [], npc: { x: 6, y: 17, name: 'Thiên Tướng Giữ Cổng' }
  },
  sky_peach: {
    id: 'sky_peach', name: 'Vườn Bàn Đào', realm: 'Thiên Giới', theme: 'heaven', w: 58, h: 38, seed: 91, trees: 0.16, ponds: 5, safe: false, enter: 'skyPeach',
    portals: [{ x: 0, to: 'sky', tx: 60, ty: null }, { x: 57, to: 'sky_camp', tx: 3, ty: null }],
    mobs: [{ tpl: 'yeuhau', n: 12 }, { tpl: 'thienbinh', n: 5 }], road: [{ tpl: 'yeuhau', n: 4 }], fixed: [], npc: { x: 6, y: 16, name: 'Tiên Nữ Bàn Đào' }
  },
  sky_camp: {
    id: 'sky_camp', name: 'Thiên Binh Doanh', realm: 'Thiên Giới', theme: 'heaven', w: 60, h: 40, seed: 97, trees: 0.03, ponds: 1, safe: false, enter: 'skyCamp',
    portals: [{ x: 0, to: 'sky_peach', tx: 54, ty: null }, { x: 59, to: 'sky_thunder', tx: 3, ty: null }],
    mobs: [{ tpl: 'thientuong', n: 12 }, { tpl: 'thienbinh', n: 7 }], road: [{ tpl: 'thientuong', n: 4 }], fixed: [], npc: { x: 6, y: 16, name: 'Đô Đốc Thiên Binh' },
    teachers: [{ id: 'sword', x: 13, y: 25, name: 'Kiếm Tiên' }]
  },
  sky_thunder: {
    id: 'sky_thunder', name: 'Lôi Đình Điện', realm: 'Thiên Giới', theme: 'heaven', w: 60, h: 40, seed: 103, trees: 0.01, ponds: 3, safe: false, enter: 'skyThunder',
    portals: [{ x: 0, to: 'sky_camp', tx: 56, ty: null }, { x: 59, to: 'sky_palace', tx: 3, ty: null }],
    mobs: [{ tpl: 'loilinh', n: 12 }, { tpl: 'thientuong', n: 4 }], road: [{ tpl: 'loilinh', n: 4 }], fixed: [], npc: { x: 6, y: 16, name: 'Lôi Công' },
    teachers: [{ id: 'thunder', x: 13, y: 25, name: 'Lôi Pháp Tiên Nhân' }]
  },
  sky_palace: {
    id: 'sky_palace', name: 'Lăng Tiêu Bảo Điện', realm: 'Thiên Giới', theme: 'heaven', w: 48, h: 32, seed: 109, trees: 0.01, ponds: 0, safe: true, enter: 'skyPalace',
    portals: [{ x: 0, to: 'sky_thunder', tx: 56, ty: null }], mobs: [], road: [], fixed: [], npc: { x: 24, y: 12, name: 'Ngọc Hoàng Thượng Đế' }
  },
  // Điện Diêm Vương là phòng báo cáo riêng, không sinh quái và không có cổng gây lạc tuyến.
  dien_yama: {
    id: 'dien_yama', name: 'Điện Diêm Vương', realm: 'Âm Giới', theme: 'hell', w: 32, h: 22, seed: 113, trees: 0, ponds: 0, safe: true, enter: 'yamaReport',
    spawn: { x: 16, y: 15 }, spawnArea: { x: 16, y: 15 }, portals: [{ x: 31, to: 'sky', tx: 3, ty: null }], mobs: [], road: [], fixed: [],
    npc: { x: 16, y: 9, name: 'Diêm Vương' }
  }
};
const MAPS = {};
for (const id in MAP_DEFS) MAPS[id] = buildMap(MAP_DEFS[id]);
// Mã map dạng số dùng cho lệnh admin /goto 1..12, theo đúng tuyến cốt truyện.
const MAP_ORDER = ['town','field','forest','duong','am','hbdien','daidien','sky','sky_peach','sky_camp','sky_thunder','sky_palace','dien_yama'];
const MAP_NUMBER = Object.fromEntries(MAP_ORDER.map((id, i) => [String(i + 1), id]));

// Luật mở khóa map: trả về null nếu được vào, hoặc câu thông báo nếu bị chặn.
const GATES = {
  q1: p => p.q.d[0] ? null : 'Ải Rừng Sương Mù đang bị phong tỏa. Hoàn thành nhiệm vụ 1 (Sên Xanh → Heo Rừng → Khủng Long) để mở.',
  quests: p => p.q.open ? null : 'Cổng Âm Giới bị phong ấn. Hãy hoàn thành đủ 5 nhiệm vụ ở Dân Gian để mở khóa.',
  road16: p => p.lv >= 16 && p.q.open ? null : 'Đại Lộ Âm Dương chỉ mở từ cấp 16 và sau khi hoàn thành 5 nhiệm vụ Dân Gian.',
  pass: p => p.q.pass ? null : 'Cổng Âm Giới cần Thẻ Thông Hành. Hãy đánh quái và boss tại Đại Lộ Âm Dương.',
  palace: p => p.q.amStage >= 3 ? null : 'Hắc Bạch Vô Thường chưa dẫn bạn vào Đại Điện.',
  lv16: p => p.lv >= 16 ? null : 'Thiên Giới chỉ dành cho Vệ Binh Cao Cấp (cấp 16 trở lên).',
  skyStart: p => p.q.book ? null : 'Cổng Nam Thiên Môn chỉ mở khi bạn nhận Hắc Quỷ Bình Điển và hoàn thành Âm Giới.',
  skyPeach: p => p.q.skyStage >= 1 ? null : 'Vườn Bàn Đào chỉ mở sau khi hoàn thành thử thách Nam Thiên Môn.',
  skyCamp: p => p.q.skyStage >= 2 ? null : 'Thiên Binh Doanh chỉ mở sau khi hoàn thành nhiệm vụ Vườn Bàn Đào.',
  skyThunder: p => p.q.skyStage >= 3 ? null : 'Lôi Đình Điện chỉ mở sau khi vượt qua Thiên Binh Doanh.',
  skyPalace: p => p.q.skyStage >= 4 ? null : 'Lăng Tiêu Bảo Điện chỉ mở sau khi vượt qua Lôi Đình Điện.',
  yamaReport: p => p.q.amStage >= 5 ? null : 'Điện Diêm Vương chỉ mở sau khi đánh bại Hắc Vọng Oan Linh.'
};
const mapAllowed = (p, mapId) => { const e = MAPS[mapId] && MAPS[mapId].enter; return !e || !GATES[e](p); };

const MOB_TPL = {
  slime: { name: 'Sên Xanh', lv: 1, hp: 30, atk: 4, exp: 9, speed: 42, aggro: 130, gold: [1, 4], r: 11 },
  boar: { name: 'Heo Rừng', lv: 3, hp: 80, atk: 9, exp: 24, speed: 70, aggro: 150, gold: [3, 9], r: 13 },
  dino: { name: 'Khủng Long', lv: 5, hp: 220, atk: 13, exp: 48, speed: 68, aggro: 150, gold: [5, 12], r: 16 },
  wolf: { name: 'Sói Xám', lv: 6, hp: 150, atk: 16, exp: 55, speed: 96, aggro: 190, gold: [6, 16], r: 13 },
  phi: { name: 'Phì Lũ', lv: 7, hp: 260, atk: 14, exp: 62, speed: 48, aggro: 140, gold: [8, 18], r: 15 },
  ent: { name: 'Mộc Nhân', lv: 9, hp: 360, atk: 28, exp: 150, speed: 52, aggro: 160, gold: [14, 32], r: 16 },
  bwolf: { name: 'Sói Chúa', lv: 8, boss: true, hp: 700, atk: 22, exp: 320, speed: 96, aggro: 230, gold: [40, 70], r: 22 },
  bent: { name: 'Mộc Vương', lv: 10, boss: true, hp: 1300, atk: 30, exp: 600, speed: 54, aggro: 220, gold: [70, 110], r: 26 },
  bking: { name: 'Đại Ma Vương', lv: 12, boss: true, hp: 2200, atk: 40, exp: 1100, speed: 66, aggro: 260, gold: [120, 180], r: 28 },
  ghost: { name: 'Hồn Ma', lv: 10, hp: 320, atk: 22, exp: 130, speed: 70, aggro: 190, gold: [15, 34], r: 13 },
  vonglinh: { name: 'Vong Linh', lv: 16, hp: 560, atk: 34, exp: 260, speed: 72, aggro: 200, gold: [25, 48], r: 14 },
  quysai: { name: 'Quỷ Sai', lv: 16, hp: 620, atk: 38, exp: 300, speed: 76, aggro: 210, gold: [28, 55], r: 15 },
  quigac: { name: 'Quỷ Gác Cổng', lv: 17, hp: 720, atk: 42, exp: 340, speed: 70, aggro: 210, gold: [35, 65], r: 16 },
  chungquy: { name: 'Chung Quỳ', lv: 18, boss: true, hp: 5200, atk: 95, exp: 900, speed: 62, aggro: 280, gold: [180, 300], r: 29 },
  oanlinh: { name: 'Hắc Vọng Oan Linh', lv: 20, boss: true, hp: 6200, atk: 78, exp: 1400, speed: 54, aggro: 260, gold: [220, 380], r: 30 },
  broad: { name: 'Trấn Lộ Quỷ Tướng', lv: 18, boss: true, hp: 4300, atk: 72, exp: 850, speed: 65, aggro: 260, gold: [150, 280], r: 28 },
  skeleton: { name: 'Bộ Xương', lv: 12, hp: 480, atk: 30, exp: 190, speed: 62, aggro: 170, gold: [22, 48], r: 14 },
  demon: { name: 'Ác Quỷ', lv: 15, hp: 760, atk: 42, exp: 320, speed: 78, aggro: 200, gold: [34, 70], r: 15 },
  byama: { name: 'Diêm Vương', lv: 18, boss: true, hp: 3800, atk: 58, exp: 2200, speed: 60, aggro: 280, gold: [250, 400], r: 30 },
  angel: { name: 'Thiên Binh', lv: 18, hp: 900, atk: 50, exp: 420, speed: 80, aggro: 200, gold: [45, 90], r: 14 },
  qilin: { name: 'Kỳ Lân', lv: 22, hp: 1300, atk: 66, exp: 700, speed: 100, aggro: 220, gold: [70, 130], r: 16 },
  titan: { name: 'Thiên Tướng', lv: 26, hp: 1900, atk: 84, exp: 1100, speed: 60, aggro: 200, gold: [100, 190], r: 17 },
  bsky: { name: 'Thiên Tướng Trấn Thiên', lv: 29, boss: true, hp: 7500, atk: 105, exp: 5000, speed: 70, aggro: 300, gold: [500, 800], r: 32 },
  thienbinh: { name: 'Thiên Binh', lv: 21, hp: 1500, atk: 58, exp: 560, speed: 82, aggro: 210, gold: [60, 110], r: 15 },
  yeuhau: { name: 'Yêu Hầu Giữ Đào', lv: 23, hp: 1850, atk: 68, exp: 720, speed: 100, aggro: 230, gold: [75, 140], r: 16 },
  thientuong: { name: 'Thiên Tướng', lv: 26, hp: 2500, atk: 82, exp: 1050, speed: 68, aggro: 230, gold: [100, 180], r: 18 },
  loilinh: { name: 'Lôi Linh', lv: 28, hp: 2800, atk: 92, exp: 1250, speed: 88, aggro: 240, gold: [120, 200], r: 17 },
  bloithan: { name: 'Lôi Thần', lv: 30, boss: true, hp: 10500, atk: 125, exp: 6500, speed: 66, aggro: 310, gold: [650, 950], r: 32 },
  mathan: { name: 'Ma Thần Phản Thiên', lv: 35, boss: true, hp: 18000, atk: 155, exp: 12000, speed: 72, aggro: 340, gold: [1200, 1800], r: 36 }
};
const WEAPONS = [
  { tier: 0, name: 'Vũ khí gỗ', atk: 3 },
  { tier: 1, name: 'Vũ khí sắt', atk: 9 },
  { tier: 2, name: 'Vũ khí thép', atk: 18 },
  { tier: 3, name: 'Vũ khí lam tinh', atk: 32 },
  { tier: 4, name: 'Vũ khí huyền thiết', atk: 50 },
  { tier: 5, name: 'Vũ khí thiên kim', atk: 75 }
];
const CLASSES = {
  warrior: { label: 'Kiếm sĩ', base: 10, perLv: 3, hpBase: 90, hpPerLv: 22, range: 62, cd: 550 },
  archer: { label: 'Cung thủ', base: 8, perLv: 2.6, hpBase: 70, hpPerLv: 16, range: 220, cd: 650 }
};
const POTION_PRICE = 15;
const SKILL_DEFS = {
  palm: { name: 'Chưởng Ma Lực', desc: 'Phóng chưởng lực hắc ám, gây sát thương diện rộng quanh nhân vật.', map: 'duong', teacher: 'Ma Đạo Sư', minLv: 16, minStage: 0, cost: 120, cooldown: 5000 },
  thunder: { name: 'Triệu Hồi Sấm Sét', desc: 'Gọi sét đánh vào cụm quái gần nhất, gây sát thương lớn trong vùng.', map: 'sky_thunder', teacher: 'Lôi Pháp Tiên Nhân', minLv: 24, minStage: 3, cost: 500, cooldown: 9000 },
  sword: { name: 'Vạn Kiếm Quy Tông', desc: 'Triệu hồi kiếm trận, chém nhiều mục tiêu xung quanh.', map: 'sky_camp', teacher: 'Kiếm Tiên', minLv: 26, minStage: 3, cost: 800, cooldown: 14000 }
};
function cleanSkills(raw, q) {
  const out = { palm: false, thunder: false, sword: false };
  if (raw && typeof raw === 'object') for (const k of Object.keys(out)) out[k] = !!raw[k];
  // Tương thích nhân vật cũ đã nhận Hắc Quỷ Bình Điển.
  if (q && q.book) out.palm = true;
  return out;
}
function sendSkills(p) { send(p, { t: 'skills', learned: p.skills, defs: SKILL_DEFS }); }


const tileAt = (m, x, y) => (x < 0 || y < 0 || x >= m.w || y >= m.h) ? '#' : m.grid[y][x];
const blocked = c => c === '#' || c === '~';
function canStand(m, px, py, r) {
  return !blocked(tileAt(m, Math.floor((px - r) / TILE), Math.floor((py - r) / TILE))) &&
    !blocked(tileAt(m, Math.floor((px + r) / TILE), Math.floor((py - r) / TILE))) &&
    !blocked(tileAt(m, Math.floor((px - r) / TILE), Math.floor((py + r) / TILE))) &&
    !blocked(tileAt(m, Math.floor((px + r) / TILE), Math.floor((py + r) / TILE)));
}
function spawnPoint(m, tx, ty) {
  const y = ty == null ? m.midY : ty;
  return { x: tx * TILE + TILE / 2, y: y * TILE + TILE / 2 };
}

// ---------------------------------------------------------------- thế giới
let nextId = 1;
const players = new Map(); // id -> player
const byName = new Map();  // tên thường -> player
const mobs = [];
const drops = [];
const events = {}; // mapId -> [sự kiện trong tick này]
for (const id in MAPS) events[id] = [];

function randInt(a, b) { return a + Math.floor(Math.random() * (b - a + 1)); }
function randomSpot(m) {
  for (let i = 0; i < 200; i++) {
    const x = randInt(10, m.w - 11), y = randInt(2, m.h - 3);
    const px = x * TILE + TILE / 2, py = y * TILE + TILE / 2;
    if (canStand(m, px, py, 14)) return { x: px, y: py };
  }
  return { x: m.w * TILE / 2, y: m.h * TILE / 2 };
}
function roadSpot(m) {
  for (let i = 0; i < 50; i++) {
    const x = randInt(10, m.w - 11), y = m.midY + randInt(-1, 1);
    const px = x * TILE + TILE / 2, py = y * TILE + TILE / 2;
    if (canStand(m, px, py, 14)) return { x: px, y: py };
  }
  return randomSpot(m);
}
function spawnMob(mapId, tpl, x, y) {
  const t = MOB_TPL[tpl];
  mobs.push({
    id: nextId++, tpl, map: mapId, x, y, hx: x, hy: y, hp: t.hp, mhp: t.hp, dead: false, respawnAt: 0,
    target: null, atkAt: 0, wx: 0, wy: 0, wanderUntil: 0
  });
}
for (const id in MAPS) {
  const m = MAPS[id];
  for (const g of (m.mobs || [])) for (let i = 0; i < g.n; i++) { const p = randomSpot(m); spawnMob(id, g.tpl, p.x, p.y); }
  for (const g of m.road || []) for (let i = 0; i < g.n; i++) { const p = roadSpot(m); spawnMob(id, g.tpl, p.x, p.y); }
  for (const f of m.fixed || []) { if (f.tpl === 'chungquy' || f.tpl === 'oanlinh') continue; spawnMob(id, f.tpl, f.x * TILE + TILE / 2, f.y * TILE + TILE / 2); }
}

const maxHp = p => CLASSES[p.cls].hpBase + p.lv * CLASSES[p.cls].hpPerLv + gearTotals(p).hp;
const attackPower = p => Math.round(CLASSES[p.cls].base + p.lv * CLASSES[p.cls].perLv +
  (p.weapon >= 0 ? WEAPONS[p.weapon].atk : 0) + gearTotals(p).atk);
const clampHp = p => { p.hp = Math.min(p.hp, maxHp(p)); };

function send(p, obj) { if (p.ws && p.ws.readyState === 1) p.ws.send(JSON.stringify(obj)); }
function sys(p, m) { send(p, { t: 'sys', m }); }
function ev(mapId, e) { events[mapId].push(e); }

function joinMap(p, mapId, tx, ty) {
  const m = MAPS[mapId];
  const pt = spawnPoint(m, tx, ty);
  p.map = mapId; p.x = pt.x; p.y = pt.y; p.dx = 0; p.dy = 0;
  // Khôi phục Boss nhiệm vụ nếu người chơi đăng nhập lại/đổi map giữa chừng.
  if (mapId === 'daidien' && p.q.amStage === 3 && p.q.amGate >= 10 && !mobs.some(x => x.map === 'daidien' && x.tpl === 'chungquy'))
    spawnMob('daidien', 'chungquy', 34 * TILE + TILE / 2, 16 * TILE + TILE / 2);
  if (mapId === 'daidien' && p.q.amStage === 4 && !mobs.some(x => x.map === 'daidien' && x.tpl === 'oanlinh'))
    spawnMob('daidien', 'oanlinh', 42 * TILE + TILE / 2, 16 * TILE + TILE / 2);
  const mt = {};
  // Gửi đầy đủ metadata để cả Boss được triệu hồi động giữa trận cũng hiển thị đúng tên và thanh máu.
  for (const tpl in MOB_TPL) { const t = MOB_TPL[tpl]; mt[tpl] = { n: t.name, r: t.r, b: t.boss ? 1 : 0 }; }
  const c = o => o ? { x: o.x * TILE + TILE / 2, y: o.y * TILE + TILE / 2 } : null;
  send(p, { t: 'map', id: m.id, name: m.name, realm: m.realm, theme: m.theme, w: m.w, h: m.h, rows: m.rows, safe: !!m.safe,
    shop: c(m.shop), npc: m.npc ? { ...c(m.npc), n: m.npc.name } : null, teachers: (m.teachers || []).map(t => ({ ...c(t), n: t.name, id: t.id })), cage: c(m.cage), mt });
}

// ---------------------------------------------------------------- túi đồ
function sendInv(p) {
  const eq = {};
  for (const s of SLOT_KEYS) eq[s] = p.eq[s] ? itemView(p.eq[s]) : null;
  send(p, { t: 'inv', cap: BAG_CAP, bag: p.bag.map(itemView), eq, keys: p.keys });
}
function dropItem(mapId, x, y, kind, v, label, owner) {
  drops.push({ id: nextId++, map: mapId, x: x + randInt(-14, 14), y: y + randInt(-14, 14), kind, v, label, owner, ttl: 60000 });
}
function giveItem(p, it) {
  if (p.bag.length < BAG_CAP) { p.bag.push(it); sys(p, 'Nhận được ' + itemTitle(it) + '.'); }
  else { dropItem(p.map, p.x, p.y, 'gear', it, ''); sys(p, 'Túi đồ đầy! ' + itemTitle(it) + ' rơi dưới chân bạn.'); }
}

// ---------------------------------------------------------------- nhiệm vụ (Dân Gian)
const Q1_STAGES = [
  { tpl: 'slime', n: 10, txt: 'Hạ 10 Sên Xanh' },
  { tpl: 'boar', n: 5, txt: 'Hạ 5 Heo Rừng' },
  { tpl: 'dino', n: 3, txt: 'Hạ 3 Khủng Long' }
];
const QUESTS = [
  { title: 'Dọn sạch Đồng Cỏ', reward: { exp: 150, gold: 60, gear: ['top', 1, 1] } },
  { title: 'Chìa Khóa Vàng', reward: { exp: 100, gold: 40, pot: 3 } },
  { title: 'Luyện tập', reward: { gold: 100, gear: ['boots', 1, 1] } },
  { title: 'Săn quái thú', reward: { exp: 200, gold: 80, gear: ['bottom', 1, 1] } },
  { title: 'Giải cứu công chúa', reward: { exp: 600, gold: 300, gear: ['top', 2, 1] } }
];
function defaultQuest() { return { st: 0, c1: 0, c4: 0, d: [false, false, false, false, false], open: false, pass: false, amStage: 0, amGhost: 0, amSai: 0, amGate: 0, book: false, skyStage: 0, skyCount: 0 }; }
function cleanQuest(q) {
  const d = defaultQuest();
  if (!q) return d;
  if (Array.isArray(q.d)) d.d = [0, 1, 2, 3, 4].map(i => !!q.d[i]);
  d.st = Math.max(0, Math.min(2, q.st | 0)); d.c1 = Math.max(0, q.c1 | 0); d.c4 = Math.max(0, q.c4 | 0);
  d.open = d.d.every(Boolean);
  d.pass = !!q.pass; d.amStage = Math.max(0, Math.min(6, q.amStage | 0));
  d.amGhost = Math.max(0, q.amGhost | 0); d.amSai = Math.max(0, q.amSai | 0); d.amGate = Math.max(0, q.amGate | 0); d.book = !!q.book; d.skyStage = Math.max(0, Math.min(6, q.skyStage | 0)); d.skyCount = Math.max(0, q.skyCount | 0);
  return d;
}
function rewardText(r) {
  const a = [];
  if (r.exp) a.push(r.exp + ' EXP');
  if (r.gold) a.push(r.gold + ' vàng');
  if (r.pot) a.push(r.pot + ' bình máu');
  if (r.gear) { const v = itemView({ s: r.gear[0], r: r.gear[1], t: r.gear[2] }); a.push(v.name + ' (' + v.rn + ')'); }
  return a.join(', ');
}
function questList(p) {
  const q = p.q, st = Q1_STAGES[Math.min(q.st, 2)];
  const rows = [
    q.d[0] ? { desc: 'Đã hạ đủ Sên Xanh, Heo Rừng, Khủng Long. Ải Rừng Sương Mù đã mở.', cur: 1, max: 1 }
      : { desc: st.txt + ' (bước ' + (q.st + 1) + '/3). Xong sẽ qua ải mới.', cur: q.c1, max: st.n },
    { desc: 'Tìm Chìa Khóa Vàng: rơi ngẫu nhiên (25%) khi hạ Phì Lũ trong Rừng Sương Mù.', cur: q.d[1] ? 1 : 0, max: 1 },
    { desc: 'Luyện tập để đạt cấp 5.', cur: Math.min(p.lv, 5), max: 5 },
    { desc: 'Đánh 10 quái thú.', cur: Math.min(q.c4, 10), max: 10 },
    { desc: 'Giải cứu công chúa ở lồng giam cuối Rừng Sương Mù (cần Chìa Khóa Vàng, bấm F gần lồng). Dọc đường có nhiều quái và boss chặn lối.', cur: q.d[4] ? 1 : 0, max: 1 }
  ];
  const out = rows.map((r, i) => ({ id: i + 1, title: QUESTS[i].title, desc: r.desc, cur: r.cur, max: r.max, done: q.d[i], rw: rewardText(QUESTS[i].reward) }));
  const am = [
    {title:'Âm Giới I — Thẻ Thông Hành',desc:'Tại Đại Lộ Âm Dương, hạ 10 Hồn Ma để mở đường thách đấu Trấn Lộ Quỷ Tướng.',cur:q.amGhost,max:10,done:q.amStage>0,rw:'Mở khóa Boss'},
    {title:'Âm Giới II — Vong Linh',desc:'Đánh bại Trấn Lộ Quỷ Tướng và nhặt Thẻ Thông Hành, sau đó vào Hoang Mạc Hồn và hạ 10 Vong Linh.',cur:q.amSai,max:10,done:q.amStage>1,rw:'1–2 cấp'},
    {title:'Âm Giới III — Hắc Bạch Vô Thường',desc:'Sau khi hạ đủ 10 Vong Linh, bạn được dịch chuyển đến Điện Dẫn Hồn. Hãy nói chuyện với Hắc Vô Thường và Bạch Vô Thường.',cur:q.amStage>=2?1:0,max:1,done:q.amStage>2,rw:'Dẫn vào Đại Điện'},
    {title:'Âm Giới IV — Đại Điện U Minh',desc:'Hạ 10 Quỷ Gác Cổng, sau đó đến gần Chung Quỳ và chịu thất bại theo cốt truyện để được đưa đến nhiệm vụ tiếp theo.',cur:q.amGate,max:10,done:q.amStage>3,rw:'Mở nhiệm vụ Hắc Vọng'},
    {title:'Âm Giới V — Hắc Vọng Oan Linh',desc:'Sau khi Chung Quỳ đánh bại bạn, hạ Hắc Vọng Oan Linh tại Đại Điện U Minh. Bạn sẽ được chuyển đến Điện Diêm Vương để báo cáo và nhận Hắc Quỷ Bình Điển.',cur:q.amStage>=5?1:0,max:1,done:q.book,rw:'Hắc Quỷ Bình Điển'}
  ];
  am.forEach((r,i)=>out.push({id:6+i,title:r.title,desc:r.desc,cur:Math.min(r.cur,r.max),max:r.max,done:r.done,rw:r.rw}));
  const sky = [
    {title:'Thiên Giới I — Nam Thiên Môn',desc:'Sau khi nhận Hắc Quỷ Bình Điển, đến Nam Thiên Môn và hạ 10 Thiên Binh.',cur:q.skyStage===0?q.skyCount:10,max:10,done:q.skyStage>0,rw:'Mở Vườn Bàn Đào'},
    {title:'Thiên Giới II — Vườn Bàn Đào',desc:'Vượt qua Vườn Bàn Đào, hạ 8 Yêu Hầu Giữ Đào.',cur:q.skyStage===1?q.skyCount:8,max:8,done:q.skyStage>1,rw:'Mở Thiên Binh Doanh'},
    {title:'Thiên Giới III — Thiên Binh Doanh',desc:'Hạ 10 Thiên Tướng để chứng minh thực lực trước thiên quân.',cur:q.skyStage===2?q.skyCount:10,max:10,done:q.skyStage>2,rw:'Mở Lôi Đình Điện'},
    {title:'Thiên Giới IV — Lôi Đình Điện',desc:'Hạ 8 Lôi Linh và đánh bại Lôi Thần.',cur:q.skyStage===3?q.skyCount:8,max:8,done:q.skyStage>3,rw:'Mở Lăng Tiêu Bảo Điện'},
    {title:'Thiên Giới V — Phán Quyết Cửu Trùng',desc:'Đến Lăng Tiêu Bảo Điện, thưa chuyện với Ngọc Hoàng và đánh bại Ma Thần Phản Thiên.',cur:q.skyStage>=6?1:0,max:1,done:q.skyStage>=6,rw:'Hoàn thành cốt truyện'}
  ];
  sky.forEach((r,i)=>out.push({id:11+i,title:r.title,desc:r.desc,cur:Math.min(r.cur,r.max),max:r.max,done:r.done,rw:r.rw}));
  return out;
}
function sendQuests(p) { send(p, { t: 'q', list: questList(p), open: p.q.open }); }
function finishQuest(p, i) {
  const q = p.q;
  if (q.d[i]) return;
  q.d[i] = true;
  const def = QUESTS[i], r = def.reward;
  sys(p, 'Hoàn thành nhiệm vụ ' + (i + 1) + ': ' + def.title + '! Thưởng: ' + rewardText(r) + '.');
  if (r.gold) p.gold += r.gold;
  if (r.pot) p.potions += r.pot;
  if (r.gear) giveItem(p, { s: r.gear[0], r: r.gear[1], t: r.gear[2] });
  if (i === 0) sys(p, 'Ải mới đã mở: Rừng Sương Mù ở phía đông Đồng Cỏ Xanh!');
  if (r.exp) addExp(p, r.exp);
  if (q.d.every(Boolean) && !q.open) {
    q.open = true;
    sys(p, 'Cả 5 nhiệm vụ đã xong! Ải Âm Giới được mở khóa: đi hết Rừng Sương Mù về phía đông.');
  }
  sendQuests(p); sendInv(p);
}
function checkQuests(p) {
  if (!p.q.d[2] && p.lv >= 5) finishQuest(p, 2);
  if (!p.q.d[3] && p.q.c4 >= 10) finishQuest(p, 3);
}
function questKill(p, tpl) {
  const q = p.q;
  if (!q.d[0]) {
    const st = Q1_STAGES[q.st];
    if (st.tpl === tpl) {
      q.c1++;
      if (q.c1 >= st.n) {
        if (q.st >= Q1_STAGES.length - 1) { q.c1 = st.n; finishQuest(p, 0); }
        else { q.st++; q.c1 = 0; sys(p, 'Xong bước ' + q.st + '/3. Tiếp theo: ' + Q1_STAGES[q.st].txt + '.'); }
      }
    }
  }
  if (!q.d[3]) q.c4++;
  checkQuests(p);
  sendQuests(p);
}

function completeAmStage(p, stage) {
  if (p.q.amStage >= stage) return;
  p.q.amStage = stage;
  const before = p.lv; addExp(p, Math.max(0, expNeed(p.lv) * 1.35));
  if (p.lv < before + 1) { p.lv = Math.min(MAX_LEVEL, p.lv + 1); p.exp = 0; p.hp = maxHp(p); }
  sys(p, 'Hoàn thành nhiệm vụ Âm Giới ' + stage + '! Bạn được tăng cấp và hồi đầy HP.');
  sendQuests(p);
}

// ---------------------------------------------------------------- NPC
function hintLine(p) {
  const l = questList(p).find(x => !x.done);
  return l ? 'Việc cần làm lúc này — ' + l.title + ': ' + l.desc + ' (' + l.cur + '/' + l.max + ')'
    : 'Bạn đã hoàn thành cả 5 nhiệm vụ Dân Gian. Hãy tiến về Âm Giới!';
}
function npcLines(p, m) {
  switch (m.id) {
    case 'town': return [
      'Chào mừng, lữ khách! Ta là Trưởng Làng Mộc. Đây là Dân Gian, nơi mọi hành trình bắt đầu.',
      'Điều khiển: WASD hoặc mũi tên để đi, Space để đánh, phím 1 dùng bình máu, F nói chuyện với NPC, B mua bình máu ở thương nhân, Enter để chat.',
      'Bấm H mở Nhà Chính, E xem Trang bị, I mở Túi đồ, Q xem Nhiệm vụ. Quái sẽ rơi Áo, Quần, Giày với độ hiếm Thường, Hiếm và Thần Thoại. Nhớ mặc chúng vào!',
      'Cấp bậc: cấp 1-3 Dân Thường, 4-6 Chiến Binh, 7-10 Chiến Binh Cao Cấp, 11-15 Vệ Binh, 16-20 Vệ Binh Cao Cấp, 21-25 Vệ Binh Hoàng Gia, 26-30 Mãnh Tướng. Cấp càng cao càng cần nhiều EXP.',
      'Ở Dân Gian có 5 nhiệm vụ. Làm xong cả 5 thì ải Âm Giới sẽ mở. Hãy đi qua cổng tím phía đông để đến Đồng Cỏ Xanh.',
      hintLine(p)];
    case 'field': return [
      'Ta là Thợ Săn Bảy. Đồng Cỏ Xanh đầy Sên Xanh, Heo Rừng và cả Khủng Long to xác.',
      'Nhiệm vụ 1 làm theo thứ tự: 10 Sên Xanh, rồi 5 Heo Rừng, rồi 3 Khủng Long. Xong là cổng phía đông sang Rừng Sương Mù sẽ mở.',
      'Mẹo: máu thấp thì lùi ra và uống bình máu (phím 1). Đồ quái rơi ra nhớ nhặt, rồi mở Túi đồ (I) để mặc.',
      hintLine(p)];
    case 'forest': return [
      'Ta là lính canh sống sót của Rừng Sương Mù. Cẩn thận, nơi này rất nguy hiểm.',
      'Hạ Phì Lũ có 25% rơi Chìa Khóa Vàng. Chìa này chỉ mình bạn thấy và nhặt được.',
      'Công chúa bị nhốt trong lồng giam ở cuối đường. Dọc đường có Sói Chúa, Mộc Vương và Đại Ma Vương chặn lối, cùng rất nhiều quái. Đến gần lồng, bấm F để mở khóa.',
      'Xong cả 5 nhiệm vụ, cổng phía đông sau lồng giam sẽ dẫn tới Âm Giới.',
      hintLine(p)];
    case 'duong': return ['Ta là Lý Bạch, người dẫn đường giữa hai cõi. Đại Lộ Âm Dương chỉ dành cho người cấp 16 trở lên.', p.q.amStage === 0 ? 'Hãy hạ 10 Hồn Ma để phá phong ấn gọi Trấn Lộ Quỷ Tướng.' : 'Trấn Lộ Quỷ Tướng canh giữ Thẻ Thông Hành. Hạ hắn và nhặt thẻ để mở cổng Hoang Mạc Hồn.', 'Muốn học Chưởng Ma Lực, hãy tìm Ma Đạo Sư ở phía nam Đại Lộ Âm Dương.'];
    case 'am':
      if (p.q.amStage === 1) return ['Ta là Lý Bạch. Hoang Mạc Hồn đã mở nhờ Thẻ Thông Hành.', 'Hãy hạ 10 Vong Linh. Khi hoàn thành, Hắc Bạch Vô Thường sẽ triệu gọi ngươi.'];
      return ['Ta là Lý Bạch. Hãy tiếp tục hành trình Âm Giới.'];
    case 'hbdien': return ['Hắc Vô Thường: Sinh hồn đã vượt qua cửa ải, đứng trước Điện Dẫn Hồn.', 'Bạch Vô Thường: Chúng ta sẽ mở lối đưa ngươi đến Đại Điện U Minh. Hãy chuẩn bị tinh thần đối mặt với phán xét.'];
    case 'daidien':
      if (p.q.amStage === 3 && p.q.amGate < 10) return ['Ta là Lý Bạch. Hắc Bạch Vô Thường đã đưa bạn vào Đại Điện U Minh.', 'Hãy hạ đủ 10 Quỷ Gác Cổng. Sau đó Chung Quỳ sẽ xuất hiện ở cuối điện.'];
      if (p.q.amStage === 3 && p.q.amGate >= 10) return ['Mười Quỷ Gác Cổng đã bị tiêu diệt. Chung Quỳ đã xuất hiện!', 'Hãy đến gần Chung Quỳ. Theo thiên mệnh, ngươi phải nhận thất bại trước hắn để được đưa đến thử thách kế tiếp.'];
      if (p.q.amStage === 4) return ['Chung Quỳ đã đánh bại ngươi và mở phong ấn cuối điện.', 'Hắc Vọng Oan Linh đã xuất hiện trong Đại Điện. Hãy tiêu diệt nó, sau đó ngươi sẽ được triệu đến Điện Diêm Vương để báo cáo.'];
      return ['Ta là Lý Bạch. Hãy tiếp tục hành trình Âm Giới.'];
    case 'dien_yama': return ['Ta là Diêm Vương, chủ quản U Minh.', 'Hắc Vọng Oan Linh đã bị tiêu diệt. Hãy báo cáo rõ sự việc để nhận phán thưởng và Hắc Quỷ Bình Điển.'];
    case 'sky': return ['Ta là Thiên Tướng Giữ Cổng. Nam Thiên Môn là cửa ải đầu tiên của Cửu Trùng Thiên.', 'Hạ 10 Thiên Binh để chứng minh ngươi đủ tư cách bước vào Vườn Bàn Đào.', 'Thiên Giới chỉ mở với người đã nhận Hắc Quỷ Bình Điển từ Diêm Vương.'];
    case 'sky_peach': return ['Ta là Tiên Nữ Bàn Đào. Vườn đào tiên đang bị Yêu Hầu chiếm giữ.', 'Hạ 8 Yêu Hầu Giữ Đào để mở đường đến Thiên Binh Doanh.'];
    case 'sky_camp': return ['Ta là Đô Đốc Thiên Binh. Thiên quân không dễ dàng công nhận người phàm.', 'Hạ 10 Thiên Tướng. Sau đó cổng Lôi Đình Điện sẽ mở.', 'Kiếm Tiên ở phía nam doanh trại có thể truyền thụ Vạn Kiếm Quy Tông khi ngươi đủ cấp và tiến trình.'];
    case 'sky_thunder': return ['Ta là Lôi Công. Lôi Đình Điện đang mất kiểm soát.', 'Hạ 8 Lôi Linh và đánh bại Lôi Thần để mở Lăng Tiêu Bảo Điện.', 'Lôi Pháp Tiên Nhân ở phía nam điện có thể dạy Triệu Hồi Sấm Sét.'];
    case 'sky_palace': return ['Ngươi đã vượt qua Cửu Trùng Thiên và đến trước Ngọc Hoàng Thượng Đế.', 'Hãy chuẩn bị đối mặt Ma Thần Phản Thiên — mối họa cuối cùng đe dọa cả Tam Giới.'];
    default: return ['Hãy tiếp tục hành trình của mình.'];
  }
}
function talk(p) {
  if (p.dead) return;
  const m = MAPS[p.map];
  const near = o => o && Math.hypot(o.x * TILE + TILE / 2 - p.x, o.y * TILE + TILE / 2 - p.y) <= 120;
  if (near(m.cage)) return cageTalk(p);
  const teacher = (m.teachers || []).find(t => near(t));
  if (teacher) return talkTeacher(p, teacher);
  if (near(m.npc)) {
    if (m.id === 'hbdien' && p.q.amStage === 2) {
      p.q.amStage = 3; addExp(p, Math.max(0, expNeed(p.lv) * 1.2));
      joinMap(p, 'daidien', 6, 16); sendQuests(p);
      return send(p, { t:'talk', name:'Hắc Bạch Vô Thường', portrait:'hbdien', lines:['Hắc Vô Thường: Phàm nhân đã vượt qua cửa ải Hoang Mạc Hồn. Ta sẽ mở đường cho ngươi tiến vào Đại Điện U Minh.', 'Bạch Vô Thường: Hãy hạ 10 Quỷ Gác Cổng. Sau đó đến gặp Chung Quỳ; ngươi phải nhận bại dưới tay ngài để được triệu đến thử thách cuối.'] });
    }
    if (m.id === 'hbdien' && p.q.amStage >= 3) return send(p, { t:'talk', name:'Hắc Bạch Vô Thường', portrait:'hbdien', lines:['Hắc Vô Thường: Con đường phía trước đã mở. Đừng để âm khí mê hoặc tâm trí.', 'Bạch Vô Thường: Hãy hoàn thành phán xét tại Đại Điện U Minh. Chúng ta sẽ luôn dõi theo hành trình của ngươi.'] });
    if (m.id === 'dien_yama' && p.q.amStage === 5 && !p.q.book) {
      p.q.book = true; p.q.amStage = 6; p.skills.palm = true;
      sys(p, 'Diêm Vương đã ghi nhận chiến công và trao Hắc Quỷ Bình Điển — mở khóa Ma Cầu Hắc Ám Chưởng!');
      sendQuests(p); sendSkills(p); sendInv(p);
      return send(p,{t:'talk',name:'Diêm Vương',portrait:'yama',lines:['Bổn Vương đã nhận được báo cáo. Hắc Vọng Oan Linh đã bị trừ diệt, U Minh tạm yên.', 'Ban thưởng cho ngươi Hắc Quỷ Bình Điển. Từ nay ngươi có thể lĩnh hội Ma Cầu Hắc Ám Chưởng. Cổng Nam Thiên Môn đã mở; hãy tiếp tục hành trình lên Thiên Giới.']});
    }
    if (m.id === 'dien_yama' && p.q.book) return send(p,{t:'talk',name:'Diêm Vương',portrait:'yama',lines:['Công lao của ngươi đã được ghi vào sổ công đức U Minh.', 'Hắc Quỷ Bình Điển đã thuộc về ngươi. Cổng Nam Thiên Môn đang chờ phía trước.']});
    if (m.id === 'sky_palace' && p.q.skyStage === 4) { p.q.skyStage = 5; const exists = mobs.some(x=>x.map==='sky_palace' && x.tpl==='mathan' && !x.dead); if (!exists) spawnMob('sky_palace','mathan', 34*TILE+TILE/2, 16*TILE+TILE/2); sendQuests(p); return send(p,{t:'talk',name:'Ngọc Hoàng Thượng Đế',portrait:'jade',lines:['Ngươi đã vượt qua các cửa ải Thiên Giới. Nhưng Ma Thần Phản Thiên đang phá vỡ phong ấn Tam Giới.', 'Hãy đánh bại Ma Thần Phản Thiên để chấm dứt đại kiếp. Đây là thử thách cuối cùng!']}); }
    if (m.id === 'sky_palace' && p.q.skyStage >= 6) return send(p,{t:'talk',name:'Ngọc Hoàng Thượng Đế',portrait:'jade',lines:['Tam Giới đã thái bình. Công lao của ngươi sẽ được lưu danh trên Thiên Bảng.', 'Ngươi đã hoàn thành toàn bộ hành trình từ Dân Gian, Âm Giới đến Thiên Giới.']});
    return send(p, { t: 'talk', name: m.npc.name, lines: npcLines(p, m) });
  }
  sys(p, 'Không có ai ở gần để nói chuyện.');
}
function talkTeacher(p, teacher) {
  const def = SKILL_DEFS[teacher.id];
  if (!def) return;
  if (p.skills[teacher.id]) return send(p, { t: 'talk', name: teacher.name, lines: ['Ngươi đã lĩnh hội ' + def.name + '.', def.desc, 'Mở bảng Kỹ năng hoặc dùng nút kỹ năng trên màn hình để thi triển.'] });
  const stage = teacher.id === 'palm' ? (p.q.open ? 0 : -1) : p.q.skyStage;
  if (p.lv < def.minLv || stage < def.minStage) return send(p, { t: 'talk', name: teacher.name, lines: ['Muốn học ' + def.name + ', ngươi cần đạt cấp ' + def.minLv + ' và hoàn thành đúng cửa ải.', 'Yêu cầu tiến trình: ' + (teacher.id === 'palm' ? 'mở khóa Âm Giới' : 'Thiên Giới giai đoạn ' + def.minStage + ' trở lên') + '.', 'Khi đủ điều kiện, hãy quay lại gặp ta.'] });
  if (p.gold < def.cost) return send(p, { t: 'talk', name: teacher.name, lines: ['Bí thuật ' + def.name + ' cần ' + def.cost + ' vàng để truyền thụ.', 'Hiện ngươi chỉ có ' + p.gold + ' vàng. Hãy tích lũy rồi quay lại.'] });
  p.gold -= def.cost; p.skills[teacher.id] = true;
  if (teacher.id === 'palm' && p.q.book) p.skills.palm = true;
  sys(p, 'Đã học tuyệt kỹ ' + def.name + '! Mở bảng Kỹ năng hoặc dùng nút cảm ứng để thi triển.');
  sendSkills(p); sendInv(p);
  send(p, { t: 'talk', name: teacher.name, lines: ['Ta đã truyền thụ ' + def.name + ' cho ngươi.', def.desc, 'Tuyệt kỹ đã được mở khóa. Hãy luyện tập thành thạo!'] });
}

function cageTalk(p) {
  if (p.q.d[4]) return send(p, { t: 'talk', name: 'Công chúa', lines: ['Cảm ơn bạn đã cứu ta! Cổng phía đông dẫn đến Âm Giới, hãy cẩn thận nhé.'] });
  if (p.keys < 1) return send(p, { t: 'talk', name: 'Lồng giam', lines: [
    'Lồng bị khóa bằng ổ khóa vàng. Bạn cần Chìa Khóa Vàng, rơi ngẫu nhiên khi hạ Phì Lũ trong Rừng Sương Mù.',
    'Công chúa: Làm ơn, hãy cứu ta với!'] });
  p.keys--;
  finishQuest(p, 4);
  send(p, { t: 'talk', name: 'Công chúa', lines: [
    'Cạch! Chiếc Chìa Khóa Vàng xoay trong ổ khóa và cửa lồng bật mở.',
    'Ta tự do rồi! Cảm ơn dũng sĩ. Xin hãy nhận phần thưởng này.',
    p.q.open ? 'Cổng Âm Giới ở phía đông đã mở cho bạn. Chúc may mắn!' : 'Hãy hoàn thành nốt các nhiệm vụ còn lại để mở cổng Âm Giới.'] });
}

// ---------------------------------------------------------------- kinh nghiệm, quái chết
function addExp(p, amount) {
  p.exp += amount;
  while (p.lv < MAX_LEVEL && p.exp >= expNeed(p.lv)) {
    p.exp -= expNeed(p.lv);
    p.lv++;
    p.hp = maxHp(p);
    ev(p.map, { k: 'lvl', x: p.x, y: p.y, id: p.id });
    sys(p, 'Lên cấp ' + p.lv + '! HP hồi đầy.' + (RANKS.some(r => r[0] === p.lv) ? ' Bạn thăng bậc: ' + rankOf(p.lv) + '!' : ''));
  }
  if (p.lv >= MAX_LEVEL) p.exp = 0;
  checkQuests(p);
}
function killMob(mob, p) {
  const t = MOB_TPL[mob.tpl];
  mob.dead = true; mob.target = null; mob.respawnAt = Date.now() + (t.boss ? 60000 : 8000);
  let xp = t.exp;
  if (p.lv - t.lv > 5) xp = Math.max(1, Math.floor(xp / 2));
  addExp(p, xp);
  ev(mob.map, { k: 'die', x: mob.x, y: mob.y });
  dropItem(mob.map, mob.x, mob.y, 'gold', randInt(t.gold[0], t.gold[1]), '');
  if (Math.random() < 0.22) dropItem(mob.map, mob.x, mob.y, 'potion', 1, '');
  const tier = Math.floor(t.lv / 5) + (t.boss ? 1 : 0);
  if (t.boss) {
    dropItem(mob.map, mob.x, mob.y, 'potion', 1, '');
    dropItem(mob.map, mob.x, mob.y, 'gear', rollGear(tier, true), '');
    for (const o of players.values()) if (o.map === mob.map) sys(o, p.name + ' đã hạ boss ' + t.name + '!');
  } else if (Math.random() < 0.09) {
    dropItem(mob.map, mob.x, mob.y, 'gear', rollGear(tier, false), '');
  }
  if (Math.random() < 0.07) {
    const wt = Math.min(WEAPONS.length - 1, Math.floor((t.lv - 1) / 5) + (Math.random() < 0.25 ? 1 : 0));
    dropItem(mob.map, mob.x, mob.y, 'weapon', wt, WEAPONS[wt].name);
  }
  // Chìa Khóa Vàng: 25% khi hạ Phì Lũ, chỉ người đánh thấy và nhặt được
  if (mob.tpl === 'phi' && p.keys < 1 && !p.q.d[4] && Math.random() < 0.25) {
    dropItem(mob.map, mob.x, mob.y, 'key', 1, '', p.id);
    sys(p, 'Phì Lũ làm rơi một Chìa Khóa Vàng! Hãy nhặt lấy.');
  }
  if (mob.map === 'duong' && mob.tpl === 'broad' && !p.q.pass && p.q.amStage >= 1 && p.q.amGhost >= 10) { dropItem('duong', mob.x, mob.y, 'pass', 1, '', p.id); sys(p, 'Trấn Lộ Quỷ Tướng đã rơi Thẻ Thông Hành! Hãy bước đến nhặt lấy.'); }
  if (mob.map === 'duong' && mob.tpl === 'ghost' && p.q.amStage === 0) { p.q.amGhost++; if (p.q.amGhost >= 10) { p.q.amGhost = 10; completeAmStage(p, 1); sys(p, 'Phong ấn đã vỡ! Trấn Lộ Quỷ Tướng xuất hiện trên Đại Lộ Âm Dương. Hãy đánh bại hắn để lấy Thẻ Thông Hành.'); } else sendQuests(p); }
  if (mob.map === 'am' && mob.tpl === 'vonglinh' && p.q.amStage === 1) { p.q.amSai++; if (p.q.amSai >= 10) { p.q.amSai = 10; completeAmStage(p, 2); joinMap(p, 'hbdien', 15, 14); sys(p, 'Bạn đã hạ đủ 10 Vong Linh và được triệu hồi đến Điện Dẫn Hồn. Hãy nói chuyện với Hắc Bạch Vô Thường.'); } else sendQuests(p); }
  if (mob.map === 'daidien' && mob.tpl === 'quigac' && p.map === 'daidien' && p.q.amStage === 3) {
    p.q.amGate = Math.min(10, p.q.amGate + 1);
    if (p.q.amGate >= 10) {
      const exists = mobs.some(x => x.map === 'daidien' && x.tpl === 'chungquy');
      if (!exists) spawnMob('daidien', 'chungquy', 34 * TILE + TILE / 2, 16 * TILE + TILE / 2);
      sys(p, 'Đã hạ đủ 10 Quỷ Gác Cổng! Chung Quỳ đã xuất hiện ở trung tâm Đại Điện. Hãy đến gần ngài để tiếp tục cốt truyện.');
    }
    sendQuests(p);
  }
  if (mob.map === 'daidien' && mob.tpl === 'oanlinh' && p.map === 'daidien' && p.q.amStage === 4) {
    p.q.amStage = 5; addExp(p, Math.max(0, expNeed(p.lv) * 1.5));
    joinMap(p, 'dien_yama', 16, 15);
    sys(p, 'Hắc Vọng Oan Linh đã bị tiêu diệt! Bạn được triệu đến Điện Diêm Vương. Hãy đến gần Diêm Vương và chạm Tương tác để báo cáo.');
    sendQuests(p);
  }
  if (mob.map === 'sky' && mob.tpl === 'thienbinh' && p.q.skyStage === 0) { p.q.skyCount++; if (p.q.skyCount >= 10) { p.q.skyCount = 0; p.q.skyStage = 1; sys(p, 'Nam Thiên Môn đã được khai thông! Cổng Vườn Bàn Đào mở ra.'); } sendQuests(p); }
  if (mob.map === 'sky_peach' && mob.tpl === 'yeuhau' && p.q.skyStage === 1) { p.q.skyCount++; if (p.q.skyCount >= 8) { p.q.skyCount = 0; p.q.skyStage = 2; sys(p, 'Vườn Bàn Đào đã được giải cứu! Thiên Binh Doanh mở cửa.'); } sendQuests(p); }
  if (mob.map === 'sky_camp' && mob.tpl === 'thientuong' && p.q.skyStage === 2) { p.q.skyCount++; if (p.q.skyCount >= 10) { p.q.skyCount = 0; p.q.skyStage = 3; sys(p, 'Thiên Binh Doanh đã công nhận thực lực của bạn. Lôi Đình Điện mở cửa.'); } sendQuests(p); }
  if (mob.map === 'sky_thunder' && mob.tpl === 'loilinh' && p.q.skyStage === 3) { p.q.skyCount++; if (p.q.skyCount >= 8) { p.q.skyCount = 8; const exists = mobs.some(x=>x.map==='sky_thunder' && x.tpl==='bloithan' && !x.dead); if (!exists) spawnMob('sky_thunder','bloithan', 50*TILE+TILE/2, 20*TILE+TILE/2); sys(p, 'Đã dọn sạch Lôi Linh! Lôi Thần xuất hiện, hãy đánh bại hắn để mở Lăng Tiêu Bảo Điện.'); } sendQuests(p); }
  if (mob.map === 'sky_thunder' && mob.tpl === 'bloithan' && p.q.skyStage === 3 && p.q.skyCount >= 8) { p.q.skyStage = 4; addExp(p, Math.max(0, expNeed(p.lv) * 2)); sys(p, 'Lôi Thần đã bị đánh bại! Lăng Tiêu Bảo Điện mở cửa.'); sendQuests(p); }
  if (mob.map === 'sky_palace' && mob.tpl === 'mathan' && p.q.skyStage === 5) { p.q.skyStage = 6; addExp(p, Math.max(0, expNeed(p.lv) * 5)); p.gold += 3000; sys(p, 'MA THẦN PHẢN THIÊN ĐÃ BỊ ĐÁNH BẠI! Tam Giới thái bình. Bạn đã hoàn thành cốt truyện cuối cùng và nhận 3.000 vàng.'); sendQuests(p); sendInv(p); }
  questKill(p, mob.tpl);
}
function killPlayer(p) {
  if (p.map === 'daidien' && p.q.amStage === 3 && p.q.amGate >= 10) {
    p.q.amStage = 4; p.hp = 1; addExp(p, Math.max(0, expNeed(p.lv) * 1.2));
    const exists = mobs.some(x => x.map === 'daidien' && x.tpl === 'oanlinh');
    if (!exists) spawnMob('daidien', 'oanlinh', 42 * TILE + TILE / 2, 16 * TILE + TILE / 2);
    joinMap(p, 'daidien', 7, 15);
    sys(p, 'Chung Quỳ đã đánh bại bạn theo phán quyết! Hắc Vọng Oan Linh xuất hiện trong Đại Điện. Hãy tiêu diệt nó để được triệu đến Điện Diêm Vương.');
    sendQuests(p); return;
  }
  p.dead = true; p.respawnAt = Date.now() + 3000; p.dx = 0; p.dy = 0;
  ev(p.map, { k: 'die', x: p.x, y: p.y });
  sys(p, 'Bạn bị hạ gục. Sẽ hồi sinh ở làng sau 3 giây.');
}

// ---------------------------------------------------------------- vòng lặp
function movePlayers(dt) {
  for (const p of players.values()) {
    if (p.dead) continue;
    const m = MAPS[p.map], now = Date.now();
    let dx = p.dx, dy = p.dy;
    const len = Math.hypot(dx, dy);
    // cổng bị khóa coi như tường, kèm thông báo
    const portalDeny = (nx, ny) => {
      if (tileAt(m, Math.floor(nx / TILE), Math.floor(ny / TILE)) !== 'P') return false;
      const right = nx > m.w * TILE / 2;
      const portal = m.portals.find(q => (q.x > m.w / 2) === right);
      const dest = portal && MAPS[portal.to], msg = dest && dest.enter && GATES[dest.enter](p);
      if (!msg) return false;
      if (now - p.gateAt > 2500) { p.gateAt = now; sys(p, msg); }
      return true;
    };
    if (len > 0) {
      if (len > 1) { dx /= len; dy /= len; }
      const sp = (BASE_SPEED + gearTotals(p).spd) * dt;
      const nx = p.x + dx * sp, ny = p.y + dy * sp;
      if (canStand(m, nx, p.y, 10) && !portalDeny(nx, p.y)) p.x = nx;
      if (canStand(m, p.x, ny, 10) && !portalDeny(p.x, ny)) p.y = ny;
      if (Math.abs(dx) > 0.2 || Math.abs(dy) > 0.2) {
        p.dir = Math.abs(dx) > Math.abs(dy) ? (dx > 0 ? 'r' : 'l') : (dy > 0 ? 'd' : 'u');
      }
      // cổng dịch chuyển
      if (tileAt(m, Math.floor(p.x / TILE), Math.floor(p.y / TILE)) === 'P') {
        const right = p.x > m.w * TILE / 2;
        const portal = m.portals.find(q => (q.x > m.w / 2) === right);
        if (portal) {
          joinMap(p, portal.to, portal.tx, portal.ty);
          sys(p, 'Bạn đến ' + MAPS[portal.to].realm + ' - ' + MAPS[portal.to].name + '.');
        }
      }
    }
    // hồi máu khi không bị đánh
    if (p.hp < maxHp(p) && now - p.hurtAt > (m.safe ? 0 : 5000)) {
      p.hp = Math.min(maxHp(p), p.hp + maxHp(p) * (m.safe ? 0.08 : 0.015) * dt);
    }
    // nhặt đồ
    for (let i = drops.length - 1; i >= 0; i--) {
      const d = drops[i];
      if (d.map !== p.map || Math.hypot(d.x - p.x, d.y - p.y) > 26) continue;
      if (d.owner && d.owner !== p.id) continue;
      if (d.kind === 'gold') { p.gold += d.v; sys(p, '+' + d.v + ' vàng'); }
      else if (d.kind === 'potion') { p.potions += d.v; sys(p, '+1 Bình máu'); }
      else if (d.kind === 'pass') { p.q.pass = true; sys(p, 'Đã nhận Thẻ Thông Hành! Cổng Âm Giới mở ra.'); sendQuests(p); }
      else if (d.kind === 'key') {
        if (p.keys >= 1) continue;
        p.keys = 1; sys(p, 'Nhặt được Chìa Khóa Vàng!');
        if (!p.q.d[1]) finishQuest(p, 1);
        sendInv(p);
      } else if (d.kind === 'gear') {
        if (p.bag.length >= BAG_CAP) {
          if (now - p.fullAt > 2500) { p.fullAt = now; sys(p, 'Túi đồ đã đầy! Hãy bán hoặc mặc bớt đồ.'); }
          continue;
        }
        p.bag.push(d.v); sys(p, 'Nhặt được ' + itemTitle(d.v) + '.'); sendInv(p);
      } else if (d.kind === 'weapon') {
        if (d.v > p.weapon) { p.weapon = d.v; sys(p, 'Trang bị ' + WEAPONS[d.v].name + ' (+' + WEAPONS[d.v].atk + ' sát thương).'); }
        else { const g = 10 + d.v * 10; p.gold += g; sys(p, WEAPONS[d.v].name + ' không tốt hơn, bán được ' + g + ' vàng.'); }
      }
      ev(p.map, { k: 'pick', x: d.x, y: d.y });
      drops.splice(i, 1);
    }
  }
}
function updateMobs(dt) {
  const now = Date.now();
  for (const mob of mobs) {
    const t = MOB_TPL[mob.tpl], m = MAPS[mob.map];
    if (mob.dead) {
      if (now >= mob.respawnAt) { mob.dead = false; mob.hp = mob.mhp; mob.x = mob.hx; mob.y = mob.hy; mob.target = null; }
      continue;
    }
    // chọn mục tiêu
    let target = mob.target ? players.get(mob.target) : null;
    if (target && (target.dead || (target.isAdmin && target.god) || target.map !== mob.map || (mob.tpl === 'broad' && target.q.amStage < 1) || Math.hypot(target.x - mob.x, target.y - mob.y) > 420 ||
        Math.hypot(mob.hx - mob.x, mob.hy - mob.y) > 520)) { target = null; mob.target = null; }
    if (!target) {
      let best = t.aggro;
      for (const p of players.values()) {
        if (p.dead || (p.isAdmin && p.god) || p.map !== mob.map || (mob.tpl === 'broad' && p.q.amStage < 1)) continue;
        const d = Math.hypot(p.x - mob.x, p.y - mob.y);
        if (d < best) { best = d; target = p; }
      }
      mob.target = target ? target.id : null;
    }
    let vx = 0, vy = 0;
    if (target) {
      const dx = target.x - mob.x, dy = target.y - mob.y, d = Math.hypot(dx, dy);
      if (d > t.r + 14) { vx = dx / d; vy = dy / d; }
      else if (now >= mob.atkAt && !(target.isAdmin && target.god)) {
        mob.atkAt = now + 1000;
        const raw = t.atk * (0.8 + Math.random() * 0.4);
        const dmg = Math.max(1, Math.round(raw * 100 / (100 + gearTotals(target).def * 1.5)));
        target.hp -= dmg; target.hurtAt = now;
        ev(mob.map, { k: 'hit', x: target.x, y: target.y - 18, v: dmg, me: target.id });
        if (target.hp <= 0) { target.hp = 0; killPlayer(target); mob.target = null; }
      }
    } else {
      // đi lang thang quanh chỗ sinh
      if (now >= mob.wanderUntil) {
        mob.wanderUntil = now + randInt(1200, 3500);
        const a = Math.random() * Math.PI * 2, still = Math.random() < 0.4;
        mob.wx = still ? 0 : Math.cos(a) * 0.5; mob.wy = still ? 0 : Math.sin(a) * 0.5;
        if (Math.hypot(mob.hx - mob.x, mob.hy - mob.y) > 140) {
          const d = Math.hypot(mob.hx - mob.x, mob.hy - mob.y);
          mob.wx = (mob.hx - mob.x) / d * 0.6; mob.wy = (mob.hy - mob.y) / d * 0.6;
        }
      }
      vx = mob.wx; vy = mob.wy;
    }
    if (vx || vy) {
      const nx = mob.x + vx * t.speed * dt, ny = mob.y + vy * t.speed * dt;
      if (canStand(m, nx, mob.y, t.r - 2)) mob.x = nx;
      if (canStand(m, mob.x, ny, t.r - 2)) mob.y = ny;
    }
  }
  for (let i = drops.length - 1; i >= 0; i--) { drops[i].ttl -= TICK_MS; if (drops[i].ttl <= 0) drops.splice(i, 1); }
  for (const p of players.values()) {
    if (p.dead && now >= p.respawnAt) {
      p.dead = false; p.hp = maxHp(p); p.hurtAt = 0;
      joinMap(p, 'town', MAP_DEFS.town.spawn.x, MAP_DEFS.town.spawn.y);
    }
  }
}

function attack(p) {
  if (p.dead) return;
  if (p.map === 'daidien' && p.q.amStage === 3 && p.q.amGate >= 10) { const cq = mobs.find(m=>m.map==='daidien' && m.tpl==='chungquy' && !m.dead); if(cq && Math.hypot(cq.x-p.x,cq.y-p.y)<150) { killPlayer(p); return; } }
  const now = Date.now(), cls = CLASSES[p.cls];
  if (now < p.atkAt) return;
  p.atkAt = now + cls.cd;
  let best = null, bd = cls.range;
  for (const mob of mobs) {
    if (mob.dead || mob.map !== p.map || (mob.tpl === 'broad' && p.q.amStage < 1)) continue;
    const d = Math.hypot(mob.x - p.x, mob.y - p.y) - MOB_TPL[mob.tpl].r;
    if (d < bd) { bd = d; best = mob; }
  }
  if (!best) { ev(p.map, { k: 'swing', id: p.id, x: p.x, y: p.y, dir: p.dir }); return; }
  const crit = Math.random() < 0.1;
  const dmg = p.isAdmin ? 999999999 : Math.max(1, Math.round(attackPower(p) * (0.85 + Math.random() * 0.3) * (crit ? 1.8 : 1)));
  best.hp -= dmg; best.target = p.id;
  ev(p.map, { k: 'hit', x: best.x, y: best.y - 16, v: dmg, crit, from: p.cls === 'archer' ? { x: p.x, y: p.y } : null });
  if (best.hp <= 0) killMob(best, p);
}

function castPalm(p) {
  if (p.dead) return;
  if (!p.skills.palm && !p.isAdmin) { sys(p, 'Bạn chưa học Chưởng Ma Lực. Hãy tìm Ma Đạo Sư ở Đại Lộ Âm Dương.'); return; }
  const now = Date.now(); if (now < (p.palmAt || 0)) { sys(p, 'Chưởng Ma Lực đang hồi chiêu.'); return; }
  p.palmAt = now + SKILL_DEFS.palm.cooldown;
  const dir = ({ r:[1,0], l:[-1,0], u:[0,-1], d:[0,1] })[p.dir] || [1,0];
  const length = p.q.book ? 430 : 330, width = p.q.book ? 112 : 82;
  const x1 = p.x + dir[0] * 24, y1 = p.y + dir[1] * 24;
  const x2 = p.x + dir[0] * length, y2 = p.y + dir[1] * length;
  const damage = Math.round(attackPower(p) * (p.q.book ? 3.2 : 2.0) * (p.isAdmin ? 1000 : 1));
  ev(p.map, { k:'palm', x:x1, y:y1, x2, y2, width, book:!!p.q.book });
  let hits = 0;
  for (const mob of mobs) {
    if (mob.dead || mob.map !== p.map || (mob.tpl === 'broad' && p.q.amStage < 1)) continue;
    const vx=x2-x1, vy=y2-y1, len2=vx*vx+vy*vy;
    const t=Math.max(0,Math.min(1,((mob.x-x1)*vx+(mob.y-y1)*vy)/len2));
    const px=x1+t*vx, py=y1+t*vy;
    if (Math.hypot(mob.x-px,mob.y-py) > width/2 + MOB_TPL[mob.tpl].r) continue;
    mob.hp -= damage; mob.target = p.id; hits++;
    ev(p.map,{k:'hit',x:mob.x,y:mob.y-18,v:damage,crit:false});
    if(mob.hp<=0) killMob(mob,p);
  }
  sys(p, (p.q.book ? 'Ma Cầu Hắc Ám Chưởng' : 'Chưởng Ma Lực') + ' phóng luồng hắc ám phía trước, gây ' + damage + ' sát thương (' + hits + ' mục tiêu).');
}
function castThunder(p) {
  if (p.dead) return;
  if (!p.skills.thunder && !p.isAdmin) { sys(p, 'Bạn chưa học Triệu Hồi Sấm Sét. Hãy tìm Lôi Pháp Tiên Nhân ở Lôi Đình Điện.'); return; }
  const now=Date.now(); if(now<(p.thunderAt||0)){sys(p,'Sấm Sét đang hồi chiêu.');return;}
  let target=null, best=360;
  for(const mob of mobs){if(mob.dead||mob.map!==p.map)continue;const d=Math.hypot(mob.x-p.x,mob.y-p.y);if(d<best){best=d;target=mob;}}
  if(!target){sys(p,'Không có mục tiêu trong tầm sấm sét.');return;}
  p.thunderAt=now+SKILL_DEFS.thunder.cooldown;
  const radius=100,damage=Math.round(attackPower(p)*2.8*(p.isAdmin?1000:1));
  const bolts=Array.from({length:7},(_,i)=>({x:target.x+Math.cos(i*Math.PI*2/7)*randInt(8,82),y:target.y+Math.sin(i*Math.PI*2/7)*randInt(8,82)}));ev(p.map,{k:'thunder',x:target.x,y:target.y,r:radius,bolts});let hits=0;
  for(const mob of mobs){if(mob.dead||mob.map!==p.map||Math.hypot(mob.x-target.x,mob.y-target.y)>radius+MOB_TPL[mob.tpl].r)continue;mob.hp-=damage;mob.target=p.id;hits++;ev(p.map,{k:'hit',x:mob.x,y:mob.y-18,v:damage,crit:false});if(mob.hp<=0)killMob(mob,p);}
  sys(p,'Triệu Hồi Sấm Sét gây '+damage+' sát thương lên '+hits+' mục tiêu.');
}
function castSword(p) {
  if (p.dead) return;
  if (!p.skills.sword && !p.isAdmin) { sys(p, 'Bạn chưa học Vạn Kiếm Quy Tông. Hãy tìm Kiếm Tiên ở Thiên Binh Doanh.'); return; }
  const now=Date.now();if(now<(p.swordAt||0)){sys(p,'Vạn Kiếm Quy Tông đang hồi chiêu.');return;}
  p.swordAt=now+SKILL_DEFS.sword.cooldown;const radius=245,damage=Math.round(attackPower(p)*3.5*(p.isAdmin?1000:1));
  ev(p.map,{k:'sword',x:p.x,y:p.y,r:radius,count:28});let hits=0;
  for(const mob of mobs){if(mob.dead||mob.map!==p.map||Math.hypot(mob.x-p.x,mob.y-p.y)>radius+MOB_TPL[mob.tpl].r)continue;mob.hp-=damage;mob.target=p.id;hits++;ev(p.map,{k:'hit',x:mob.x,y:mob.y-18,v:damage,crit:false});if(mob.hp<=0)killMob(mob,p);}
  sys(p,'Vạn Kiếm Quy Tông gây '+damage+' sát thương lên '+hits+' mục tiêu.');
}

function tick() {
  const dt = TICK_MS / 1000;
  movePlayers(dt);
  updateMobs(dt);
  const online = players.size;
  for (const p of players.values()) {
    const m = p.map, px = p.x, py = p.y;
    const near = (x, y) => Math.abs(x - px) < VIEW_RADIUS && Math.abs(y - py) < VIEW_RADIUS;
    const g = gearTotals(p);
    const snap = {
      t: 's', n: online,
      me: { x: Math.round(px), y: Math.round(py), hp: Math.round(p.hp), mhp: maxHp(p), lv: p.lv, exp: p.exp,
        need: p.lv >= MAX_LEVEL ? 0 : expNeed(p.lv), gold: p.gold, pot: p.potions, atk: attackPower(p),
        def: g.def, spd: BASE_SPEED + g.spd, rank: rankOf(p.lv), keys: p.keys, isAdmin: !!p.isAdmin,
        wpn: p.weapon >= 0 ? WEAPONS[p.weapon].name : 'Tay không', dead: p.dead },
      p: [], m: [], d: [], ev: events[m].filter(e => near(e.x, e.y))
    };
    for (const o of players.values()) {
      if (o.map === m && !o.dead && near(o.x, o.y)) snap.p.push([o.id, o.name, Math.round(o.x), Math.round(o.y), o.lv, Math.round(o.hp), maxHp(o), o.cls, o.dir]);
    }
    for (const mob of mobs) {
      if (mob.map === m && !mob.dead && !(mob.tpl === 'broad' && p.q.amStage < 1) && near(mob.x, mob.y)) snap.m.push([mob.id, mob.tpl, Math.round(mob.x), Math.round(mob.y), Math.round(mob.hp), mob.mhp]);
    }
    for (const d of drops) {
      if (d.map === m && near(d.x, d.y) && (!d.owner || d.owner === p.id)) snap.d.push([d.id, d.kind, Math.round(d.x), Math.round(d.y), d.v]);
    }
    send(p, snap);
  }
  for (const id in events) events[id].length = 0;
}
setInterval(tick, TICK_MS);

// ---------------------------------------------------------------- tài khoản
function hashPw(pw, salt) { return crypto.scryptSync(pw, salt, 32).toString('hex'); }
const NAME_RE = /^[\p{L}\p{N}_]{3,14}$/u;
const failures = new Map(); // ip -> {n, until}
function ipOf(req) { return req.socket.remoteAddress || '?'; }

function toRecord(p) {
  const home = spawnPoint(MAPS.town, MAP_DEFS.town.spawn.x, MAP_DEFS.town.spawn.y);
  return { lv: p.lv, exp: p.exp, hp: p.dead ? maxHp(p) : Math.max(1, Math.round(p.hp)), gold: p.gold, pot: p.potions, wpn: p.weapon,
    bag: p.bag, eq: p.eq, keys: p.keys, q: p.q, skills: p.skills,
    map: p.dead ? 'town' : p.map, x: Math.round(p.dead ? home.x : p.x), y: Math.round(p.dead ? home.y : p.y) };
}
function savePlayer(p) { if (db[p.key]) { db[p.key].ch = toRecord(p); saveDB(); } }
function removePlayer(p) {
  if (!players.has(p.id)) return;
  savePlayer(p);
  players.delete(p.id); byName.delete(p.key);
  broadcastSys(p.map, p.name + ' đã rời thế giới.', p.id);
}
function broadcastSys(mapId, m, exceptId) {
  for (const o of players.values()) if (o.map === mapId && o.id !== exceptId) sys(o, m);
}

// Tài khoản quản trị được viết cứng theo yêu cầu.
// Lưu ý: chỉ dùng repository riêng tư vì người có quyền đọc source sẽ thấy thông tin này.
const ADMIN_USERNAME = 'Vietadmin';
const ADMIN_KEY = ADMIN_USERNAME.toLowerCase();
const ADMIN_PASSWORD = 'Viet@190845';
function ensureAdminAccount() {
  if (!NAME_RE.test(ADMIN_USERNAME)) { console.error('ADMIN_USERNAME không hợp lệ.'); return; }
  if (db[ADMIN_KEY]) {
    const wasAdmin = db[ADMIN_KEY].role === 'admin';
    const salt = crypto.randomBytes(16).toString('hex');
    db[ADMIN_KEY].salt = salt; db[ADMIN_KEY].hash = hashPw(ADMIN_PASSWORD, salt); db[ADMIN_KEY].role = 'admin';
    db[ADMIN_KEY].name = ADMIN_USERNAME; db[ADMIN_KEY].cls = db[ADMIN_KEY].cls || 'warrior';
    db[ADMIN_KEY].ch = db[ADMIN_KEY].ch || {};
    const adminCh = db[ADMIN_KEY].ch;
    Object.assign(adminCh, { lv: MAX_LEVEL, exp: 0, hp: 999999, gold: 999999999, pot: 999, wpn: WEAPONS.length - 1, skills: { palm: true, thunder: true, sword: true } });
    adminCh.eq = { top: {s:'top',r:2,t:5}, bottom: {s:'bottom',r:2,t:5}, boots: {s:'boots',r:2,t:5} };
    // Chỉ reset cốt truyện admin một lần khi nâng cấp; các lần khởi động sau giữ nguyên tiến độ.
    if (!adminCh.adminQuestResetV1) { adminCh.q = defaultQuest(); adminCh.map = 'town'; adminCh.x = 0; adminCh.y = 0; adminCh.adminQuestResetV1 = true; }
    if (!wasAdmin) console.log('Đã nâng tài khoản ' + ADMIN_USERNAME + ' lên quyền admin theo cấu hình viết cứng.');
    else console.log('Đã đồng bộ tài khoản admin viết cứng trong server.js.');
    saveDB(); return;
  }
  const salt = crypto.randomBytes(16).toString('hex');
  db[ADMIN_KEY] = { name: ADMIN_USERNAME, salt, hash: hashPw(ADMIN_PASSWORD, salt), role: 'admin', cls: 'warrior',
    ch: { lv: MAX_LEVEL, exp: 0, hp: 999999, gold: 999999999, pot: 999, wpn: WEAPONS.length - 1, map: 'town', x: 0, y: 0,
      eq: { top: {s:'top',r:2,t:5}, bottom: {s:'bottom',r:2,t:5}, boots: {s:'boots',r:2,t:5} },
      skills: { palm: true, thunder: true, sword: true }, q: defaultQuest(), adminQuestResetV1: true } };
  saveDB(); console.log('Đã khởi tạo tài khoản admin viết cứng: ' + ADMIN_USERNAME + '.');
}
ensureAdminAccount();

function handleLogin(conn, ip, msg) {
  const f = failures.get(ip);
  if (f && f.until > Date.now()) return conn.fail('Đăng nhập sai quá nhiều lần. Thử lại sau 1 phút.');
  const name = String(msg.name || '').trim(), pass = String(msg.pass || ''), mode = msg.mode === 'register' ? 'register' : 'login';
  if (!NAME_RE.test(name)) return conn.fail('Tên tài khoản dài 3 đến 14 ký tự, chỉ gồm chữ, số và dấu gạch dưới.');
  if (pass.length > 64 || (mode === 'register' ? pass.length < 8 : pass.length < 4)) return conn.fail(mode === 'register' ? 'Mật khẩu đăng ký phải từ 8 đến 64 ký tự.' : 'Mật khẩu phải từ 4 đến 64 ký tự.');
  const key = name.toLowerCase();
  if (mode === 'register' && key === ADMIN_KEY) return conn.fail('Tên tài khoản này được dành riêng cho quản trị viên.');
  let acc = db[key], created = false;
  if (mode === 'register') {
    if (acc) return conn.fail('Tài khoản đã tồn tại. Hãy chuyển sang Đăng nhập.');
    const cls = msg.cls === 'archer' ? 'archer' : 'warrior';
    const salt = crypto.randomBytes(16).toString('hex');
    acc = db[key] = { name, salt, hash: hashPw(pass, salt), role: 'player', cls,
      ch: { lv: 1, exp: 0, hp: 9999, gold: 20, pot: 3, wpn: -1, map: 'town', x: 0, y: 0, skills: {} } };
    created = true; saveDB();
  } else {
    if (!acc) return conn.fail('Tài khoản chưa tồn tại. Hãy chọn Đăng ký để tạo tài khoản mới.');
    const a = Buffer.from(hashPw(pass, acc.salt), 'hex'), b = Buffer.from(acc.hash, 'hex');
    if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) {
      const ff = failures.get(ip) || { n: 0, until: 0 };
      ff.n++; if (ff.n >= 8) { ff.until = Date.now() + 60000; ff.n = 0; }
      failures.set(ip, ff);
      return conn.fail('Sai mật khẩu.');
    }
  }
  failures.delete(ip);
  const old = byName.get(key);
  if (old) { old.ws.close(4001, 'duplicate'); removePlayer(old); }
  const ch = acc.ch || {};
  const eq = {};
  for (const s of SLOT_KEYS) { const it = ch.eq && cleanItem(ch.eq[s]); eq[s] = it && it.s === s ? it : null; }
  const bag = (Array.isArray(ch.bag) ? ch.bag : []).map(cleanItem).filter(Boolean).slice(0, BAG_CAP);
  const lv = Math.max(1, Math.min(MAX_LEVEL, ch.lv | 0));
  const isAdmin = acc.role === 'admin';
  const q = cleanQuest(ch.q);
  const p = {
    id: nextId++, key, name: acc.name, cls: acc.cls === 'archer' ? 'archer' : 'warrior', ws: conn.ws, isAdmin, god: isAdmin,
    lv, exp: lv >= MAX_LEVEL ? 0 : Math.max(0, Number(ch.exp) || 0), gold: Math.max(0, Number(ch.gold) || 0),
    potions: Math.max(0, Number(ch.pot) || 0), weapon: Number.isInteger(ch.wpn) ? Math.max(-1, Math.min(ch.wpn, WEAPONS.length - 1)) : -1, hp: Number(ch.hp) || 1, map: 'town', x: 0, y: 0, dx: 0, dy: 0, dir: 'd', dead: false,
    atkAt: 0, hurtAt: 0, potAt: 0, chatAt: 0, respawnAt: 0, gateAt: 0, fullAt: 0,
    palmAt: 0, thunderAt: 0, swordAt: 0,
    bag, eq, keys: Math.min(1, ch.keys | 0), q, skills: cleanSkills(ch.skills, q)
  };
  if (isAdmin) { p.skills = { palm: true, thunder: true, sword: true }; p.gold = Math.max(p.gold, 999999999); p.potions = Math.max(p.potions, 999); p.weapon = WEAPONS.length - 1; p.eq = { top:{s:'top',r:2,t:5}, bottom:{s:'bottom',r:2,t:5}, boots:{s:'boots',r:2,t:5} }; }
  p.hp = Math.min(p.hp, maxHp(p));
  conn.player = p;
  players.set(p.id, p); byName.set(key, p);
  const mapId = MAPS[ch.map] && mapAllowed(p, ch.map) ? ch.map : 'town';
  if (created || (ch.x === 0 && ch.y === 0)) joinMap(p, 'town', MAP_DEFS.town.spawn.x, MAP_DEFS.town.spawn.y);
  else { joinMap(p, mapId, 0, 0); p.x = ch.x; p.y = ch.y; if (!canStand(MAPS[mapId], p.x, p.y, 10)) joinMap(p, 'town', MAP_DEFS.town.spawn.x, MAP_DEFS.town.spawn.y); }
  send(p, { t: 'joined', id: p.id, name: p.name, cls: p.cls, clsLabel: CLASSES[p.cls].label, created, isAdmin, ranks: RANKS, maxLv: MAX_LEVEL });
  sendInv(p); sendQuests(p); sendSkills(p);
  sys(p, isAdmin ? 'Quản trị viên đã đăng nhập. Gõ /help trong chat để xem lệnh quản trị.' : created ? 'Đăng ký thành công! Chào mừng ' + p.name + '. Hãy nói chuyện với Trưởng Làng Mộc để bắt đầu.' : 'Chào mừng trở lại, ' + p.name + '.');
  checkQuests(p);
  broadcastSys(p.map, p.name + ' vừa vào thế giới.', p.id);
}

function adminCommand(p, raw) {
  const parts = raw.trim().split(/\s+/), cmd = (parts.shift() || '').toLowerCase(), arg = parts;
  const num = (v, min, max) => { const n = Number(v); return Number.isFinite(n) ? Math.max(min, Math.min(max, Math.floor(n))) : null; };
  if (!p.isAdmin) { sys(p, 'Lệnh bắt đầu bằng / chỉ dành cho quản trị viên.'); return true; }
  if (cmd === '/help') return sys(p, 'ADMIN: /help, /maps, /players, /announce <nội dung>, /goto <số 1-13 hoặc mã>, /questreset, /level <1-30>, /gold <số>, /exp <số>, /heal, /spawn <mã_quái>, /skill all, /unlock, /kick <tên>, /save, /god on|off. Dùng /maps để xem số map.');
  if (cmd === '/maps') return sys(p, 'DANH SÁCH MAP: ' + MAP_ORDER.map((id,i)=>(i+1)+': '+MAPS[id].name+' ['+id+']').join(' | '));
  if (cmd === '/players') return sys(p, 'Đang online (' + players.size + '): ' + [...players.values()].map(x => x.name + (x.isAdmin ? ' [ADMIN]' : '') + ' @' + x.map).join(', '));
  if (cmd === '/announce') { const msg = arg.join(' ').slice(0, 180); if (!msg) return sys(p, 'Cú pháp: /announce <nội dung>'); for (const o of players.values()) sys(o, '[THÔNG BÁO] ' + msg); return true; }
  if (cmd === '/goto') { const raw = String(arg[0] || ''); const numeric = /^\d+$/.test(raw) ? String(Number(raw)) : raw; const id = MAP_NUMBER[numeric] || raw; if (!MAPS[id]) return sys(p, 'Map không hợp lệ. Gõ /maps để xem mã số 1-13.'); joinMap(p, id, MAP_DEFS[id].spawn?.x ?? 5, MAP_DEFS[id].spawn?.y ?? MAPS[id].midY); return sys(p, 'Đã dịch chuyển đến ' + MAPS[id].name + ' (map ' + (MAP_ORDER.indexOf(id)+1) + ').'); }
  if (cmd === '/level') { const n = num(arg[0], 1, MAX_LEVEL); if (n === null) return sys(p, 'Cú pháp: /level 1-30'); p.lv=n; p.exp=0; p.hp=maxHp(p); return sys(p, 'Đã đặt cấp ' + n + '.'); }
  if (cmd === '/gold') { const n = num(arg[0], 0, 1000000000); if (n === null) return sys(p, 'Cú pháp: /gold <số vàng>'); p.gold=n; sendInv(p); return sys(p, 'Đã đặt vàng: ' + n + '.'); }
  if (cmd === '/exp') { const n = num(arg[0], 0, 100000000); if (n === null) return sys(p, 'Cú pháp: /exp <số EXP>'); addExp(p,n); return sys(p, 'Đã cộng ' + n + ' EXP.'); }
  if (cmd === '/heal') { p.hp=maxHp(p); p.dead=false; p.respawnAt=0; return sys(p, 'Đã hồi đầy HP.'); }
  if (cmd === '/spawn') { const tpl=arg[0]; if (!MOB_TPL[tpl]) return sys(p, 'Mã quái không hợp lệ.'); spawnMob(p.map,tpl,p.x+70,p.y+20); return sys(p, 'Đã triệu hồi ' + MOB_TPL[tpl].name + '.'); }
  if (cmd === '/skill' && arg[0] === 'all') { p.skills={palm:true,thunder:true,sword:true}; sendSkills(p); return sys(p, 'Đã mở khóa toàn bộ tuyệt kỹ.'); }
  if (cmd === '/questreset') { p.q = defaultQuest(); p.map = 'town'; p.x = 0; p.y = 0; joinMap(p, 'town', MAP_DEFS.town.spawn.x, MAP_DEFS.town.spawn.y); sendQuests(p); savePlayer(p); return sys(p, 'Đã đặt lại toàn bộ nhiệm vụ từ đầu và đưa bạn về Làng Khởi Đầu. Cấp độ, trang bị và kỹ năng admin được giữ nguyên.'); }
  if (cmd === '/unlock') { p.q.d=[true,true,true,true,true]; p.q.open=true; p.q.pass=true; p.q.amStage=6; p.q.book=true; p.q.skyStage=6; p.skills={palm:true,thunder:true,sword:true}; sendQuests(p); sendSkills(p); return sys(p, 'Đã mở khóa toàn bộ cốt truyện và bản đồ Tam Giới.'); }
  if (cmd === '/kick') { const target=byName.get(String(arg[0]||'').toLowerCase()); if (!target || target.isAdmin) return sys(p, 'Không tìm thấy người chơi hoặc không thể kick admin.'); sys(target, 'Bạn đã bị quản trị viên ngắt kết nối.'); target.ws.close(4003,'admin kick'); removePlayer(target); return sys(p, 'Đã kick ' + target.name + '.'); }
  if (cmd === '/save') { saveDB(); return sys(p, 'Đã lưu dữ liệu tài khoản và nhân vật.'); }
  if (cmd === '/god') { p.god = arg[0] !== 'off'; return sys(p, 'Chế độ bất tử: ' + (p.god ? 'BẬT' : 'TẮT') + '.'); }
  return sys(p, 'Không rõ lệnh. Gõ /help để xem danh sách lệnh.');
}

function handleMessage(conn, ip, msg) {
  if (!msg || typeof msg.t !== 'string') return;
  if (msg.t === 'login') { if (!conn.player) handleLogin(conn, ip, msg); return; }
  const p = conn.player;
  if (!p) return;
  switch (msg.t) {
    case 'in': {
      const dx = Number(msg.dx), dy = Number(msg.dy);
      if (Number.isFinite(dx) && Number.isFinite(dy)) { p.dx = Math.max(-1, Math.min(1, dx)); p.dy = Math.max(-1, Math.min(1, dy)); }
      break;
    }
    case 'atk': attack(p); break;
    case 'palm': castPalm(p); break;
    case 'thunder': castThunder(p); break;
    case 'sword': castSword(p); break;
    case 'use': {
      const now = Date.now();
      if (p.dead || p.potions <= 0 || now < p.potAt || p.hp >= maxHp(p)) break;
      p.potAt = now + 1000; p.potions--;
      const heal = 60 + p.lv * 10;
      p.hp = Math.min(maxHp(p), p.hp + heal);
      ev(p.map, { k: 'heal', x: p.x, y: p.y - 18, v: heal });
      break;
    }
    case 'buy': {
      const m = MAPS[p.map];
      if (!m.shop || p.dead) break;
      if (Math.hypot(m.shop.x * TILE + 16 - p.x, m.shop.y * TILE + 16 - p.y) > 90) { sys(p, 'Hãy đứng gần thương nhân để mua.'); break; }
      const n = Math.max(1, Math.min(20, Number(msg.n) | 0 || 1));
      if (p.gold < POTION_PRICE) { sys(p, 'Không đủ vàng (cần ' + POTION_PRICE + ').'); break; }
      const k = Math.min(n, Math.floor(p.gold / POTION_PRICE));
      p.gold -= POTION_PRICE * k; p.potions += k; sys(p, 'Đã mua ' + k + ' Bình máu.');
      break;
    }
    case 'equip': {
      const i = Number(msg.i);
      if (!Number.isInteger(i) || i < 0 || i >= p.bag.length) break;
      const it = p.bag[i], old = p.eq[it.s];
      p.eq[it.s] = it;
      if (old) p.bag[i] = old; else p.bag.splice(i, 1);
      clampHp(p); sendInv(p);
      break;
    }
    case 'unequip': {
      const s = msg.s;
      if (!SLOTS[s] || !p.eq[s]) break;
      if (p.bag.length >= BAG_CAP) { sys(p, 'Túi đồ đã đầy, không thể tháo.'); break; }
      p.bag.push(p.eq[s]); p.eq[s] = null;
      clampHp(p); sendInv(p);
      break;
    }
    case 'sell': {
      const i = Number(msg.i);
      if (!Number.isInteger(i) || i < 0 || i >= p.bag.length) break;
      const it = p.bag[i], v = itemView(it);
      p.bag.splice(i, 1); p.gold += v.price;
      sys(p, 'Đã bán ' + itemTitle(it) + ' được ' + v.price + ' vàng.');
      sendInv(p);
      break;
    }
    case 'talk': talk(p); break;
    case 'home': {
      if (p.dead) break;
      if (p.map === 'town') { sys(p, 'Bạn đang ở Làng Khởi Đầu rồi.'); break; }
      if (Date.now() - p.hurtAt < 5000) { sys(p, 'Đang giao chiến, không thể về làng. Đợi 5 giây nữa.'); break; }
      joinMap(p, 'town', MAP_DEFS.town.spawn.x, MAP_DEFS.town.spawn.y);
      sys(p, 'Bạn đã về Làng Khởi Đầu.');
      break;
    }
    case 'chat': {
      const text = String(msg.m || '').trim().slice(0, 120);
      const now = Date.now();
      if (!text || now - p.chatAt < 700) break;
      p.chatAt = now;
      if (text.startsWith('/')) { adminCommand(p, text); break; }
      for (const o of players.values()) if (o.map === p.map) send(o, { t: 'chat', n: p.name, m: text });
      break;
    }
  }
}

// ---------------------------------------------------------------- HTTP + WebSocket
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg', '.png': 'image/png', '.webp': 'image/webp' };
const server = http.createServer((req, res) => {
  const url = req.url.split('?')[0];
  const file = url === '/' ? 'index.html' : url.slice(1);
  const full = path.join(__dirname, 'public', file);
  if (!full.startsWith(path.join(__dirname, 'public') + path.sep) || !fs.existsSync(full) || fs.statSync(full).isDirectory()) {
    res.writeHead(404); res.end('Không tìm thấy'); return;
  }
  res.writeHead(200, { 'Content-Type': MIME[path.extname(full)] || 'application/octet-stream', 'Cache-Control': 'no-cache' });
  fs.createReadStream(full).pipe(res);
});
const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 2048 });
wss.on('connection', (ws, req) => {
  const ip = ipOf(req);
  const conn = { ws, player: null, fail: m => { ws.send(JSON.stringify({ t: 'err', m })); } };
  ws.on('message', data => {
    let msg; try { msg = JSON.parse(data.toString()); } catch (e) { return; }
    try { handleMessage(conn, ip, msg); } catch (e) { console.error('Lỗi xử lý tin nhắn:', e); }
  });
  ws.on('close', () => { if (conn.player && players.get(conn.player.id) === conn.player) removePlayer(conn.player); });
  ws.on('error', () => {});
});
setInterval(() => { for (const p of players.values()) savePlayer(p); }, 30000);
function shutdown() { for (const p of players.values()) savePlayer(p); process.exit(0); }
process.on('SIGINT', shutdown); process.on('SIGTERM', shutdown);

server.listen(PORT, () => {
  console.log('Viet Legends (tác giả: Trí Việt) đang chạy: http://localhost:' + PORT);
  console.log('Mở địa chỉ trên bằng nhiều tab hoặc nhiều máy để chơi cùng nhau. Nhấn Ctrl+C để dừng.');
});

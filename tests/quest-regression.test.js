'use strict';
// Function-level regression tests for the Thiên Giới quest stages in server.js.
// Run with: node tests/quest-regression.test.js
const fs = require('fs');
const vm = require('vm');
const source = fs.readFileSync(require('path').join(__dirname, '..', 'server.js'), 'utf8');
function extractFunction(name) {
  const start = source.indexOf(`function ${name}(`);
  if (start < 0) throw new Error(`Missing function ${name}`);
  const open = source.indexOf('{', start);
  let depth = 0;
  for (let i = open; i < source.length; i++) {
    if (source[i] === '{') depth++;
    else if (source[i] === '}' && --depth === 0) return source.slice(start, i + 1);
  }
  throw new Error(`Unclosed function ${name}`);
}
function assert(condition, message) { if (!condition) throw new Error(message); }

// Validate backward-compatible migration of existing save data.
const migrationSandbox = {};
vm.createContext(migrationSandbox);
vm.runInContext(`${extractFunction('defaultQuest')}\n${extractFunction('cleanQuest')}`, migrationSandbox);
const cleanQuest = migrationSandbox.cleanQuest;
let migrated = cleanQuest({ skyStage: 1, skyCount: 3 });
assert(migrated.skyDone.join(',') === 'false,false,false', 'New/active quest state must not mark quests 12–14 complete');
migrated = cleanQuest({ skyStage: 2, skyCount: 0 });
assert(migrated.skyDone.join(',') === 'true,false,false', 'Legacy stage 2 progress must preserve quest 12 completion');
migrated = cleanQuest({ skyStage: 3, skyCount: 4 });
assert(migrated.skyDone.join(',') === 'true,true,false', 'Legacy stage 3 progress must preserve quest 12–13 completion');

const player = {
  id: 1, name: 'RegressionTester', lv: 20, exp: 0, gold: 0, keys: 0, map: 'sky_peach',
  q: { d: [false, false, false, false, false], skyStage: 1, skyCount: 0,
    skyDone: [false, false, false], amStage: 0, amGhost: 0, amSai: 0, amGate: 0 }
};
const mobs = [];
let saved = 0;
let expGranted = 0;
const sandbox = {
  MOB_TPL: {
    yeuhau: { exp: 1, lv: 10, gold: [1, 1], boss: false, name: 'Yêu Hầu Giữ Đào' },
    thientuong: { exp: 1, lv: 10, gold: [1, 1], boss: false, name: 'Thiên Tướng' },
    loilinh: { exp: 1, lv: 10, gold: [1, 1], boss: false, name: 'Lôi Linh' },
    bloithan: { exp: 1, lv: 10, gold: [1, 1], boss: true, name: 'Lôi Thần' }
  },
  players: new Map([[1, player]]), mobs, TILE: 32, WEAPONS: [{ name: 'Test sword' }],
  addExp: () => { expGranted++; }, ev: () => {}, dropItem: () => {}, randInt: () => 1, rollGear: () => ({}),
  sys: () => {}, sendQuests: () => {}, sendInv: () => {}, savePlayer: () => { saved++; },
  spawnMob: (map, tpl, x, y) => { const m = { map, tpl, x, y, hp: 10, dead: false }; mobs.push(m); return m; },
  questKill: () => {}, expNeed: () => 100, Math: Object.create(Math)
};
sandbox.Math.random = () => 1;
vm.createContext(sandbox);
vm.runInContext(extractFunction('killMob'), sandbox);
const killMob = sandbox.killMob;
function mob(map, tpl) { const m = { map, tpl, x: 100, y: 100, dead: false }; mobs.push(m); return m; }

// Quest 12: exactly 8 Yêu Hầu kills.
for (let i = 0; i < 7; i++) killMob(mob('sky_peach', 'yeuhau'), player);
assert(!player.q.skyDone[0] && player.q.skyStage === 1 && player.q.skyCount === 7, 'Quest 12 completed before 8 kills');
killMob(mob('sky_peach', 'yeuhau'), player);
assert(player.q.skyDone[0] && player.q.skyStage === 2 && player.q.skyCount === 0, 'Quest 12 did not complete at 8 kills');

// Quest 13: exactly 10 Thiên Tướng kills.
for (let i = 0; i < 9; i++) killMob(mob('sky_camp', 'thientuong'), player);
assert(!player.q.skyDone[1] && player.q.skyStage === 2 && player.q.skyCount === 9, 'Quest 13 completed before 10 kills');
killMob(mob('sky_camp', 'thientuong'), player);
assert(player.q.skyDone[1] && player.q.skyStage === 3, 'Quest 13 did not complete at 10 kills');

// Quest 14: 8 Lôi Linh spawn Lôi Thần; the boss kill completes the quest.
for (let i = 0; i < 7; i++) killMob(mob('sky_thunder', 'loilinh'), player);
assert(!player.q.skyDone[2] && player.q.skyCount === 7, 'Quest 14 completed before 8 Lôi Linh');
killMob(mob('sky_thunder', 'loilinh'), player);
assert(!player.q.skyDone[2] && player.q.skyStage === 3 && player.q.skyCount === 8, 'Quest 14 completed before Lôi Thần was defeated');
const boss = mobs.find(m => m.tpl === 'bloithan' && !m.dead);
assert(boss, 'Lôi Thần did not spawn after 8 Lôi Linh');
const beforeBossKill = expGranted;
killMob(boss, player);
assert(player.q.skyDone[2] && player.q.skyStage === 4, 'Quest 14 did not complete after Lôi Thần was defeated');
assert(expGranted === beforeBossKill + 2, 'Expected normal boss EXP plus one quest completion EXP grant');
killMob(boss, player);
assert(expGranted === beforeBossKill + 2, 'Duplicate kill awarded EXP twice');
assert(saved > 0, 'Quest progress was not persisted');
console.log('PASS: legacy migration; Q12 (8 Yêu Hầu); Q13 (10 Thiên Tướng); Q14 (8 Lôi Linh + Lôi Thần); duplicate-kill guard; save hooks');

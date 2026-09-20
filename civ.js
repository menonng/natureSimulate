'use strict';
/* ============================================================
   문명 시뮬레이터 (Civilization Simulator)
   Same engine pattern as the ecosystem sim (terrain grid + simple
   rule-based agents + tools + graph), re-skinned for people instead of
   animals, with settlements/nations/leaders/religion/ideology layered
   on top. Wrapped in an IIFE so none of its names collide with
   script.js's globals (both load as classic scripts into one page).
   ============================================================ */
(function () {

  // ---------- SEEDED RNG ---------------------------------------------------
  function hashSeed(str) {
    let h = 1779033703 ^ str.length;
    for (let i = 0; i < str.length; i++) {
      h = Math.imul(h ^ str.charCodeAt(i), 3432918353);
      h = (h << 13) | (h >>> 19);
    }
    return function () {
      h = Math.imul(h ^ (h >>> 16), 2246822507);
      h = Math.imul(h ^ (h >>> 13), 3266489909);
      h ^= h >>> 16;
      return h >>> 0;
    };
  }
  function mulberry32(a) {
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  let rng = Math.random;
  function makeRng(seedStr) {
    const h = hashSeed(String(seedStr));
    return mulberry32(h());
  }
  function rrand(a, b) { return a + rng() * (b - a); }
  function rrandInt(a, b) { return Math.floor(rrand(a, b + 1)); }
  function pick(arr) { return arr[Math.floor(rng() * arr.length)]; }

  // ---------- CONFIG ---------------------------------------------------
  const COLS = 200, ROWS = 150;
  const TICK_DT = 1 / 20;
  const MAX_TICKS_PER_FRAME = 40;

  // cell types
  const T_OCEAN = 0, T_COAST = 1, T_PLAINS = 2, T_HILLS = 3, T_MOUNTAIN = 4, T_SNOW = 5;

  const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
  const lerp = (a, b, t) => a + (b - a) * t;
  const idx = (x, y) => y * COLS + x;
  const inBounds = (x, y) => x >= 0 && x < COLS && y >= 0 && y < ROWS;

  // ---------- STATE ---------------------------------------------------
  let elevation = new Float32Array(COLS * ROWS);
  let cellType = new Uint8Array(COLS * ROWS);
  let isRiver = new Uint8Array(COLS * ROWS);
  let resource = new Float32Array(COLS * ROWS);
  let texNoise = new Float32Array(COLS * ROWS);
  // -1 = unclaimed; otherwise a nation id. One entry per land cell, giving
  // territory hard, pixel-square borders (no smoothing) at the grid's own
  // resolution, recomputed as a per-cell nearest-settlement claim.
  let territory = new Int32Array(COLS * ROWS).fill(-1);
  let territoryAccum = 0;
  const TERRITORY_INTERVAL = 2.5; // simulated seconds between automatic recomputes
  let warAccum = 0;
  const WAR_CHECK_INTERVAL = 1.4; // simulated seconds between raid checks

  let people = [];      // free-roaming, not yet settled
  let settlements = [];
  let nations = [];
  let nextId = 1;
  let nextNationHue = 0;

  const params = { resourceRegrow: 0.006, growthRate: 0.35, brushSize: 5 };
  let currentTool = 'ocean';
  let speedMultiplier = 1;
  let simTime = 0;
  let lastFrameTime = 0;
  let accumulator = 0;
  let currentSeed = '';
  let selectedNationId = null; // set by clicking a nation in the list; highlights its settlements on the map

  const history = [];
  const HISTORY_MAX = 600;
  let sampleAccum = 0;
  const SAMPLE_INTERVAL = 1.5;

  // ---------- NAME GENERATION -------------------------------------------
  // Every nation (and by extension its people, its leaders, and its ruling
  // family) is assigned one of eight naming cultures at founding: seven
  // real-world-flavored syllable banks plus 나에로크어 (Naerok), an
  // invented language built mechanically out of Korean -- see naerokify().
  const SYL_A = ['아', '카', '무', '시', '바', '노', '겔', '루', '단', '오', '테', '란', '조', '페', '힌'];
  const SYL_B = ['란', '도', '리아', '벤', '가르', '문', '자르', '엔', '실', '토', '나', '문드', '샤', '린'];
  function genName(minS, maxS) {
    const n = rrandInt(minS, maxS);
    let s = '';
    for (let i = 0; i < n; i++) s += i === 0 ? pick(SYL_A) : pick(SYL_B);
    return s;
  }
  function genReligionName() { return genName(2, 2) + pick(['교', '신앙', '도']); }

  // Hangul <-> Latin conversion, used only to build Naerok names: romanize
  // a Korean syllable block via its Unicode cho/jung/jong decomposition
  // (Revised-Romanization-style), and the reverse -- greedily reading a
  // Latin string back into Hangul the way a foreign loanword would be
  // (longest-match vowel/consonant digraphs, an epenthetic eu for a
  // stranded consonant, maximal-onset preference for codas).
  function romanizeHangul(str) {
    const ROM_CHO = ['g', 'kk', 'n', 'd', 'tt', 'r', 'm', 'b', 'pp', 's', 'ss', '', 'j', 'jj', 'ch', 'k', 't', 'p', 'h'];
    const ROM_JUNG = ['a', 'ae', 'ya', 'yae', 'eo', 'e', 'yeo', 'ye', 'o', 'wa', 'wae', 'oe', 'yo', 'u', 'wo', 'we', 'wi', 'yu', 'eu', 'ui', 'i'];
    const ROM_JONG = ['', 'k', 'k', 'k', 'n', 'n', 'n', 't', 'l', 'k', 'm', 'l', 'l', 'l', 'p', 'l', 'm', 'p', 'p', 't', 't', 'ng', 't', 't', 'k', 't', 'p', 't'];
    let out = '';
    for (const ch of str) {
      const code = ch.codePointAt(0) - 0xAC00;
      if (code < 0 || code > 11171) { out += ch; continue; }
      out += ROM_CHO[Math.floor(code / 588)] + ROM_JUNG[Math.floor((code % 588) / 28)] + ROM_JONG[code % 28];
    }
    return out;
  }
  const NAEROK_VOWELS = [['yae', 3], ['yeo', 6], ['wae', 10], ['ae', 1], ['ya', 2], ['eo', 4], ['ye', 7], ['wa', 9], ['oe', 11], ['yo', 12], ['wo', 14], ['we', 15], ['wi', 16], ['yu', 17], ['eu', 18], ['ui', 19], ['a', 0], ['e', 5], ['o', 8], ['u', 13], ['i', 20]];
  const NAEROK_CONS = [['kk', 1], ['tt', 4], ['pp', 8], ['ss', 10], ['jj', 13], ['ch', 14], ['g', 0], ['n', 2], ['d', 3], ['r', 5], ['m', 6], ['b', 7], ['s', 9], ['j', 12], ['k', 15], ['t', 16], ['p', 17], ['h', 18], ['c', 14], ['f', 17], ['l', 5], ['q', 15], ['v', 7], ['x', 15], ['z', 12]];
  const NAEROK_CODA = [['ng', 21], ['n', 4], ['m', 16], ['l', 8], ['k', 1], ['t', 7], ['p', 17], ['s', 19]];
  function hangulizeLatin(str) {
    const s = str.toLowerCase().replace(/[^a-z]/g, '');
    function matchLongest(pos, table) {
      for (const [k, v] of table) if (k && s.startsWith(k, pos)) return [k, v];
      return null;
    }
    let i = 0, result = '';
    const len = s.length;
    while (i < len) {
      let choIdx = 11; // silent onset (vowel-initial syllable)
      let vMatch = matchLongest(i, NAEROK_VOWELS);
      if (!vMatch) {
        const cMatch = matchLongest(i, NAEROK_CONS);
        if (cMatch) {
          const afterCons = i + cMatch[0].length;
          const vAfter = matchLongest(afterCons, NAEROK_VOWELS);
          if (vAfter) { choIdx = cMatch[1]; i = afterCons + vAfter[0].length; vMatch = vAfter; }
          else { choIdx = cMatch[1]; i += cMatch[0].length; vMatch = ['', 18]; } // stranded consonant -> epenthetic eu
        } else { i++; continue; }
      } else {
        i += vMatch[0].length;
      }
      const jungIdx = vMatch[1];
      let jongIdx = 0;
      const codaMatch = matchLongest(i, NAEROK_CODA);
      if (codaMatch) {
        const afterCoda = i + codaMatch[0].length;
        if (!matchLongest(afterCoda, NAEROK_VOWELS)) { jongIdx = codaMatch[1]; i = afterCoda; } // else: leave it as the next syllable's onset
      }
      result += String.fromCharCode(0xAC00 + (choIdx * 21 + jungIdx) * 28 + jongIdx);
    }
    return result || '나';
  }
  function naerokify(koreanWord) {
    const reversed = [...romanizeHangul(koreanWord)].reverse().join('');
    return hangulizeLatin(reversed);
  }

  const CULTURES = [
    { id: 'japan', label: '일본어권',
      sylA: ['아', '이', '유', '카', '키', '타', '토', '나', '노', '마', '유키', '하루', '료', '켄', '소'],
      sylB: ['토', '카', '나', '오', '미', '타', '키', '시', '노', '루', '마', '유', '라', '코', '스케'],
      familySuffix: ['야마', '모토', '카와', '사키', '하라', '시마', '무라'] },
    { id: 'slavic', label: '슬라브권',
      sylA: ['블라', '보리', '라도', '미로', '노보', '스타', '베스', '드미', '야로', '볼코', '체르', '두브'],
      sylB: ['미르', '슬라프', '노프', '친', '보', '단', '린', '토프', '예프', '고로드'],
      familySuffix: ['스키', '비치', '노프', '코프'] },
    { id: 'germanic', label: '게르만권',
      sylA: ['볼프', '하인', '프리트', '베르크', '슈타인', '하르트', '발트', '그림', '울프', '지크', '브룬'],
      sylB: ['하임', '부르크', '만', '리히', '드리히', '올트', '가르', '문트', '베르트'],
      familySuffix: ['만', '베르크', '슈타인', '하르트'] },
    { id: 'england', label: '잉글랜드',
      sylA: ['에드', '윌', '헨', '아서', '찰스', '조지', '토마스', '리처드', '로버트', '존', '알프레드', '월터', '휴'],
      sylB: ['워드', '리엄', '리', '튼', '포드', '필드', '우드', '버리', '턴'],
      familySuffix: ['턴', '포드', '필드', '우드', '버리', '스미스'] },
    { id: 'scotland', label: '스코틀랜드',
      sylA: ['던컨', '프레이저', '브루스', '스튜어트', '캠벨', '글렌', '앵거스', '말콤', '이완', '고든', '알라스데어'],
      sylB: ['도날드', '그레거', '켄지', '타비시', '클레인', '로크'],
      familyPrefix: ['맥'] },
    { id: 'usa', label: '미국',
      sylA: ['잭슨', '메이슨', '오스틴', '데일턴', '코디', '브랜든', '타일러', '라이언', '콜튼', '헌터', '케이든'],
      sylB: ['슨', '톤', '리', '든', '윈', '포드', '랜드'],
      familySuffix: ['슨', '스', '턴'] },
    { id: 'africa', label: '아프리카',
      sylA: ['콰메', '아마라', '조라', '코피', '아데', '치디', '니아', '바바', '이몰라', '세쿠', '투미', '왈레'],
      sylB: ['투', '메', '라', '디', '왈레', '니', '쿠', '분두'],
      familySuffix: ['우', '예', '이', '아'] },
    { id: 'naerok', label: '나에로크어' },
  ];
  function pickCulture() { return pick(CULTURES); }
  function culturalRoot(culture, minS, maxS) {
    const n = rrandInt(minS, maxS);
    let s = '';
    for (let i = 0; i < n; i++) s += i === 0 ? pick(culture.sylA) : pick(culture.sylB);
    return s;
  }
  const NATION_SUFFIXES = ['국', '제국', '연맹', '왕국', '공화국'];
  function genNationName(culture) {
    if (culture.id === 'naerok') return naerokify(genName(2, 3)) + pick(NATION_SUFFIXES);
    return culturalRoot(culture, 2, 3) + pick(NATION_SUFFIXES);
  }
  function genPersonName(culture) {
    if (culture.id === 'naerok') return naerokify(genName(2, 3));
    return culturalRoot(culture, 2, 3);
  }
  function genFamilyName(culture) {
    if (culture.id === 'naerok') return naerokify(genName(1, 2)) + '가';
    const root = culturalRoot(culture, 1, 2);
    if (culture.familyPrefix) return pick(culture.familyPrefix) + root + '가';
    if (culture.familySuffix) return root + pick(culture.familySuffix) + '가';
    return root + '가';
  }

  const IDEOLOGIES = ['군주제', '신정', '공화정', '전체주의', '부족연합'];
  const LEADER_TITLE = { 군주제: '왕', 신정: '대사제', 공화정: '대통령', 전체주의: '총통', 부족연합: '족장' };
  const REGIONAL_TITLE = { 군주제: '영주', 신정: '사제', 공화정: '시장', 전체주의: '지구서기', 부족연합: '촌장' };
  const CIV_TIER_NAME = ['', '석기시대', '청동기시대', '고대', '중세', '근대'];

  // How compatible two ideologies are, used both to bias inter-nation
  // diplomacy drift and to weight which ideology a drifting region is
  // likely to adopt (regions drift toward ideologies they're already
  // philosophically close to, not to a uniformly random one).
  const IDEOLOGY_AFFINITY = {
    군주제: { 군주제: 6, 신정: 4, 공화정: -4, 전체주의: -2, 부족연합: 1 },
    신정: { 군주제: 4, 신정: 6, 공화정: -2, 전체주의: -3, 부족연합: 2 },
    공화정: { 군주제: -4, 신정: -2, 공화정: 6, 전체주의: -6, 부족연합: 0 },
    전체주의: { 군주제: -2, 신정: -3, 공화정: -6, 전체주의: 3, 부족연합: -3 },
    부족연합: { 군주제: 1, 신정: 2, 공화정: 0, 전체주의: -3, 부족연합: 5 },
  };
  function personalityDiploBias(personality) {
    if (personality === '호전적' || personality === '팽창주의적' || personality === '전제적') return -1;
    if (personality === '자비로운' || personality === '실용적' || personality === '이상주의적') return 1;
    return 0;
  }

  // ---------- DIPLOMACY -------------------------------------------------
  // A continuous -100..100 score per nation pair, drifting slowly from
  // ideology affinity and leader personality plus a little noise, with
  // rare sharper "incidents". Thresholded into a label for display.
  let relations = new Map();
  let relationCls = new Map(); // previous tick's label class, for edge-detecting war/alliance
  function relationKey(a, b) { return a < b ? `${a}_${b}` : `${b}_${a}`; }
  function getRelation(aId, bId) { return relations.get(relationKey(aId, bId)) ?? 0; }
  function isAtWar(aId, bId) { return getRelation(aId, bId) < -60; }
  const REL_LABEL = (score) => {
    if (score >= 60) return { label: '동맹', cls: 'rel-ally' };
    if (score >= 20) return { label: '우호', cls: 'rel-friendly' };
    if (score >= -20) return { label: '중립', cls: 'rel-neutral' };
    if (score >= -60) return { label: '긴장', cls: 'rel-tense' };
    return { label: '전쟁', cls: 'rel-war' };
  };
  function tickDiplomacy(dt) {
    for (let i = 0; i < nations.length; i++) {
      for (let j = i + 1; j < nations.length; j++) {
        const a = nations[i], b = nations[j];
        const key = relationKey(a.id, b.id);
        let score = relations.has(key) ? relations.get(key) : rrand(-8, 8);
        const affinity = (IDEOLOGY_AFFINITY[a.ideology] && IDEOLOGY_AFFINITY[a.ideology][b.ideology]) || 0;
        const bias = affinity + personalityDiploBias(a.leader.personality) + personalityDiploBias(b.leader.personality);
        score += bias * 0.06 * dt + rrand(-0.4, 0.4) * dt;
        if (rng() < 0.00025 * dt * 20) score += rrand(-18, 18); // rare diplomatic incident
        score = clamp(score, -100, 100);
        relations.set(key, score);

        const newCls = REL_LABEL(score).cls;
        const oldCls = relationCls.get(key);
        if (newCls !== oldCls) {
          if (newCls === 'rel-war' && oldCls !== undefined) {
            pushSpeech(a, '전쟁 선포', 'war_declared', { otherName: b.name });
            pushSpeech(b, '전쟁 선포', 'war_declared', { otherName: a.name });
            showGlobalNotification(`⚔️ ${a.name}와(과) ${b.name}이(가) 전쟁을 선포했습니다.`, 'war');
          } else if (newCls === 'rel-ally' && oldCls !== undefined) {
            pushSpeech(a, '동맹 결성', 'alliance_formed', { otherName: b.name });
            pushSpeech(b, '동맹 결성', 'alliance_formed', { otherName: a.name });
          }
          relationCls.set(key, newCls);
        }
      }
    }
    const aliveIds = new Set(nations.map((n) => n.id));
    for (const key of relations.keys()) {
      const [a, b] = key.split('_').map(Number);
      if (!aliveIds.has(a) || !aliveIds.has(b)) { relations.delete(key); relationCls.delete(key); }
    }
  }

  // Leader flavor, kept separate from the nation's formal government system
  // (ideology): a personal temperament and a personal philosophical leaning,
  // randomly assigned to each leader. Used as flavor now, and as prompt
  // conditioning for the leader-speech LLM later.
  const PERSONALITIES = ['호전적', '경건한', '실용적', '고립주의적', '팽창주의적', '자비로운', '전제적', '이상주의적', '음모적', '검소한'];
  const PHILOSOPHIES = ['자유', '질서', '전통', '혁신', '명예', '부', '신앙', '정복', '평등', '혈통'];
  function genLeader(dynasty, culture) {
    return {
      name: genPersonName(culture),
      dynasty,
      personality: pick(PERSONALITIES),
      philosophy: pick(PHILOSOPHIES),
      termStart: simTime,
      termLength: rrand(90, 240), // simulated seconds before succession
    };
  }

  // ---------- LEADER SPEECHES ---------------------------------------------
  // A compositional generator stands in for the local-LLM leader speech
  // feature: each statement is freely assembled at generation time from
  // personality/philosophy/event phrase pools (never a single fixed
  // template), so within this framework -- the leader's assigned
  // personality, philosophy, ideology, and the triggering event -- the
  // wording is "free" and varies every time, while always staying in
  // character. Swapping this for a real transformers.js model later only
  // means replacing this one function's body; every call site below is
  // unaffected.
  const SPEECH_OPENERS = {
    호전적: ['우리의 힘을 두려워하라.', '나약함은 곧 죽음이다.', '적들이 떨고 있음이 느껴진다.'],
    경건한: ['신께서 우리를 인도하신다.', '이는 하늘의 뜻이다.', '경건한 마음으로 이 순간을 맞이한다.'],
    실용적: ['감정이 아니라 결과로 말하겠다.', '중요한 것은 실리다.', '우리는 냉정하게 판단해야 한다.'],
    고립주의적: ['우리 땅을 지키는 것으로 충분하다.', '먼 땅의 일은 우리와 무관하다.', '스스로를 지키는 것이 우선이다.'],
    팽창주의적: ['우리의 영토는 아직 좁다.', '더 넓은 땅이 우리를 기다린다.', '확장은 숙명이다.'],
    자비로운: ['백성의 안녕이 나의 소원이다.', '모두가 평화롭기를 바란다.', '자비로 다스리겠다.'],
    전제적: ['나의 뜻이 곧 법이다.', '의심하지 말고 따르라.', '질서는 위에서 시작된다.'],
    이상주의적: ['더 나은 세상을 꿈꾼다.', '이상은 반드시 실현된다.', '우리는 역사를 새로 쓸 것이다.'],
    음모적: ['보이지 않는 곳에서 모든 것이 결정된다.', '진실은 아는 자만이 안다.', '그림자 속에서 미소짓는다.'],
    검소한: ['사치는 우리의 적이다.', '검소함이 나라를 지킨다.', '작은 것에도 감사할 뿐이다.'],
  };
  const SPEECH_PHILOSOPHY_CLOSERS = {
    자유: ['자유가 없다면 아무 의미도 없다.', '누구도 우리를 가두지 못한다.', '스스로 선택한 길만이 옳다.'],
    질서: ['질서 없이는 번영도 없다.', '혼란은 곧 파멸이다.', '규율이 우리를 지킨다.'],
    전통: ['선조들의 길을 잊지 않겠다.', '오래된 것이 늘 낡은 것은 아니다.', '뿌리 깊은 나무는 흔들리지 않는다.'],
    혁신: ['변화를 두려워하지 않겠다.', '어제의 방식으로는 내일을 열 수 없다.', '새로움이야말로 우리의 무기다.'],
    명예: ['명예를 목숨보다 소중히 여긴다.', '부끄러운 승리보다 떳떳한 패배가 낫다.', '내 이름에 먹칠하지 않겠다.'],
    부: ['풍요로움이 곧 힘이다.', '곳간에서 인심 난다.', '부유한 나라만이 살아남는다.'],
    신앙: ['믿음이 우리를 지켜준다.', '신의 뜻은 거스를 수 없다.', '기도가 곧 우리의 힘이다.'],
    정복: ['정복만이 살길이다.', '약한 자는 가질 자격이 없다.', '땅은 취하는 자의 것이다.'],
    평등: ['모두가 평등한 세상을 만들겠다.', '누구도 특별히 우월하지 않다.', '함께 나누는 것이 옳다.'],
    혈통: ['핏줄의 이름을 더럽히지 않겠다.', '내 혈통이 곧 나의 자격이다.', '조상의 이름에 부끄럽지 않게.'],
  };
  // A leader's own signature line: deterministically picked from their
  // name+dynasty (a simple string hash, not rng()), so the same leader
  // always closes with the same personal flourish across every speech --
  // a consistent individual voice on top of the personality/philosophy/
  // event pools above, which vary every time.
  const SPEECH_SIGNATURES = [
    '나, {name}의 이름을 걸고.', '{dynasty}의 피가 증명할 것이다.', '역사가 나를 기억하리라.',
    '이것이 나의 방식이다.', '더 말할 필요는 없다.', '{name}은(는) 약속을 지킨다.',
    '내 뒤에는 {dynasty}가 있다.', '시간이 나를 증명하리라.', '나의 말은 곧 나의 검이다.',
    '{dynasty}는 흔들리지 않는다.', '{name}, 그 이름을 기억하라.', '침묵보다 행동이 낫다.',
  ];
  function hashPick(arr, seedStr) {
    let h = 0;
    for (let i = 0; i < seedStr.length; i++) h = (h * 31 + seedStr.charCodeAt(i)) >>> 0;
    return arr[h % arr.length];
  }
  const SPEECH_EVENT_CORE = {
    founding: (n) => [`${n.name}의 건국을 선포한다.`, '오늘 이 순간부터 우리는 하나의 나라다.', '이곳에 우리의 터전을 세운다.'],
    succession: (n) => [`${n.leader.dynasty}의 이름으로 이 자리에 선다.`, '선대의 뜻을 이어받아 나라를 이끌겠다.', '무거운 책임을 받아들인다.'],
    war_declared: (n, ctx) => [`${ctx.otherName}에 전쟁을 선포한다.`, `${ctx.otherName}은(는) 이제 우리의 적이다.`, `더는 ${ctx.otherName}과(와) 함께할 수 없다.`],
    alliance_formed: (n, ctx) => [`${ctx.otherName}와(과) 동맹을 맺는다.`, `이제 ${ctx.otherName}은(는) 우리의 벗이다.`, `함께라면 두려울 것이 없다.`],
    settlement_captured: (n, ctx) => [`${ctx.settlementName}을(를) 우리의 영토로 선포한다.`, `${ctx.settlementName}은(는) 이제 ${n.name}의 땅이다.`, `승리는 우리의 것이다.`],
    airstrike: (n, ctx) => [`${ctx.settlementName}에 공습을 명령했다.`, `하늘에서 심판이 내린다.`, `${ctx.settlementName} 상공에 폭격이 시작됐다.`],
    nuclear_strike: (n, ctx) => [`${ctx.settlementName}에 핵무기를 사용했다.`, `돌이킬 수 없는 선택이었다.`, `${ctx.settlementName}은(는) 이제 잿더미다.`],
    capital_relocated: (n, ctx) => [`${ctx.settlementName}을(를) 새로운 수도로 삼는다.`, `우리는 무너지지 않는다.`, `잿더미 위에서도 나라는 계속된다.`],
  };
  function generateLeaderSpeech(nation, eventType, ctx) {
    const L = nation.leader;
    const opener = pick(SPEECH_OPENERS[L.personality] || ['...']);
    const coreOptions = SPEECH_EVENT_CORE[eventType] ? SPEECH_EVENT_CORE[eventType](nation, ctx || {}) : ['...'];
    const core = pick(coreOptions);
    const closer = pick(SPEECH_PHILOSOPHY_CLOSERS[L.philosophy] || ['...']);
    const signature = hashPick(SPEECH_SIGNATURES, L.name + L.dynasty)
      .replace('{name}', L.name).replace('{dynasty}', L.dynasty);
    return `${opener} ${core} ${closer} ${signature}`.trim();
  }

  const speechLog = [];
  const SPEECH_LOG_MAX = 80;
  function pushSpeech(nation, eventLabel, eventType, ctx) {
    const text = generateLeaderSpeech(nation, eventType, ctx);
    speechLog.unshift({
      time: simTime, nationId: nation.id, nationName: nation.name, nationColor: nation.color,
      leaderName: nation.leader.name, ideology: nation.ideology, eventLabel, text,
    });
    if (speechLog.length > SPEECH_LOG_MAX) speechLog.length = SPEECH_LOG_MAX;
    if (diplomacyOpen && activeDiploTab === 'speeches') renderSpeechPanel();
  }

  // A bottom-right toast feed for events significant enough to matter to
  // the whole world, not just the nations directly involved (a routine
  // hereditary succession isn't one; a nation collapsing or a war starting
  // is). Independent of whether the 국가 정보 window is even open.
  const TOAST_MAX_VISIBLE = 5;
  function showGlobalNotification(text, type) {
    const container = document.getElementById('civToastContainer');
    if (!container) return;
    const el = document.createElement('div');
    el.className = `civToast toast-${type || 'info'}`;
    el.textContent = text;
    container.appendChild(el);
    requestAnimationFrame(() => el.classList.add('show'));
    setTimeout(() => {
      el.classList.remove('show');
      setTimeout(() => el.remove(), 400);
    }, 5500);
    while (container.children.length > TOAST_MAX_VISIBLE) container.removeChild(container.firstChild);
  }

  const NATION_HUES = [355, 25, 48, 100, 175, 210, 265, 320, 15, 130, 195, 285];
  function hslToRgb(h, s, l) {
    s /= 100; l /= 100;
    const k = (n) => (n + h / 30) % 12;
    const a = s * Math.min(l, 1 - l);
    const f = (n) => l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1)));
    return [Math.round(f(0) * 255), Math.round(f(8) * 255), Math.round(f(4) * 255)];
  }
  function nextNationColor() {
    const hue = NATION_HUES[nextNationHue % NATION_HUES.length];
    nextNationHue++;
    return { css: `hsl(${hue}, 62%, 58%)`, rgb: hslToRgb(hue, 62, 58) };
  }

  // ---------- RACES ------------------------------------------------------
  // Two playable peoples, one per source sprite character. Purely a visual +
  // demographic trait (sprite art, name, territory/nation-list bookkeeping) --
  // it does not affect individual AI behavior.
  const RACES = [
    { id: 0, name: '묘인족', frameSrc: ['assets/sprites/race0_walk0.png', 'assets/sprites/race0_walk1.png'] },
    { id: 1, name: '인간족', frameSrc: ['assets/sprites/race1_walk0.png', 'assets/sprites/race1_walk1.png'] },
  ];
  for (const race of RACES) {
    race.images = race.frameSrc.map((src) => {
      const img = new Image();
      img.src = src;
      return img;
    });
  }
  function randomRace() { return rng() < 0.5 ? 0 : 1; }
  function pickRaceFromComposition(comp) {
    if (!comp) return randomRace();
    let total = 0;
    for (const c of comp) total += c;
    if (total <= 0) return randomRace();
    let r = rng() * total;
    for (let i = 0; i < comp.length; i++) {
      r -= comp[i];
      if (r <= 0) return i;
    }
    return comp.length - 1;
  }

  // ---------- TERRAIN GENERATION -------------------------------------------

  // Value noise: random values on a coarse control-point grid, smoothly
  // interpolated up to full resolution. Summing a few octaves of this (each
  // one spanning the full 0..1 range at its own scale) gives real hills and
  // continents; a box-blur of per-pixel i.i.d. noise (the earlier approach)
  // crushes the variance almost to nothing and produces a flat, blobless mess.
  function valueNoiseLayer(w, h, cellsX, cellsY) {
    const gw = cellsX + 1, gh = cellsY + 1;
    const grid = new Float32Array(gw * gh);
    for (let i = 0; i < grid.length; i++) grid[i] = rng();
    const out = new Float32Array(w * h);
    for (let y = 0; y < h; y++) {
      const gy = (y / h) * cellsY;
      const gy0 = Math.floor(gy), gy1 = Math.min(gy0 + 1, cellsY);
      const ty = gy - gy0;
      const sy = ty * ty * (3 - 2 * ty);
      for (let x = 0; x < w; x++) {
        const gx = (x / w) * cellsX;
        const gx0 = Math.floor(gx), gx1 = Math.min(gx0 + 1, cellsX);
        const tx = gx - gx0;
        const sx = tx * tx * (3 - 2 * tx);
        const v00 = grid[gy0 * gw + gx0], v10 = grid[gy0 * gw + gx1];
        const v01 = grid[gy1 * gw + gx0], v11 = grid[gy1 * gw + gx1];
        const top = v00 + (v10 - v00) * sx;
        const bot = v01 + (v11 - v01) * sx;
        out[y * w + x] = top + (bot - top) * sy;
      }
    }
    return out;
  }

  function generateElevation() {
    const continents = valueNoiseLayer(COLS, ROWS, 7, 5);
    const regions = valueNoiseLayer(COLS, ROWS, 20, 15);
    const detail = valueNoiseLayer(COLS, ROWS, 55, 42);
    const out = new Float32Array(COLS * ROWS);
    for (let i = 0; i < out.length; i++) {
      let v = continents[i] * 0.55 + regions[i] * 0.3 + detail[i] * 0.15;
      v = clamp((v - 0.5) * 1.5 + 0.5, 0, 1); // mild contrast stretch
      out[i] = v;
    }
    return out;
  }

  const T_OCEAN_E = 0.40, T_COAST_E = 0.455, T_PLAINS_E = 0.68, T_HILLS_E = 0.82, T_MOUNTAIN_E = 0.93;
  function classify(e) {
    if (e < T_OCEAN_E) return T_OCEAN;
    if (e < T_COAST_E) return T_COAST;
    if (e < T_PLAINS_E) return T_PLAINS;
    if (e < T_HILLS_E) return T_HILLS;
    if (e < T_MOUNTAIN_E) return T_MOUNTAIN;
    return T_SNOW;
  }

  function carveRivers() {
    const count = rrandInt(10, 18);
    for (let i = 0; i < count; i++) {
      let sx = 0, sy = 0, tries = 0;
      do { sx = rrandInt(0, COLS - 1); sy = rrandInt(0, ROWS - 1); tries++; }
      while (elevation[idx(sx, sy)] < T_HILLS_E && tries < 300);
      if (tries >= 300) continue;
      let x = sx, y = sy;
      for (let step = 0; step < 500; step++) {
        isRiver[idx(x, y)] = 1;
        const e = elevation[idx(x, y)];
        if (e < T_COAST_E) break;
        let bestE = e, bx = x, by = y;
        for (let dy = -1; dy <= 1; dy++) {
          for (let dx = -1; dx <= 1; dx++) {
            if (!dx && !dy) continue;
            const nx = x + dx, ny = y + dy;
            if (!inBounds(nx, ny)) continue;
            const ne = elevation[idx(nx, ny)];
            if (ne < bestE) { bestE = ne; bx = nx; by = ny; }
          }
        }
        if (bx === x && by === y) break;
        x = bx; y = by;
      }
    }
  }

  function generateWorld(seedStr) {
    currentSeed = seedStr;
    rng = makeRng(seedStr);
    elevation = generateElevation();
    cellType = new Uint8Array(COLS * ROWS);
    isRiver = new Uint8Array(COLS * ROWS);
    resource = new Float32Array(COLS * ROWS);
    texNoise = new Float32Array(COLS * ROWS);
    for (let i = 0; i < cellType.length; i++) {
      cellType[i] = classify(elevation[i]);
      texNoise[i] = rng();
      if (cellType[i] === T_PLAINS) resource[i] = rrand(0.3, 0.85);
      else if (cellType[i] === T_COAST) resource[i] = rrand(0.2, 0.55);
      else if (cellType[i] === T_HILLS) resource[i] = rrand(0.15, 0.45);
    }
    carveRivers();

    people = [];
    settlements = [];
    nations = [];
    relations = new Map();
    relationCls = new Map();
    warAccum = 0;
    speechLog.length = 0;
    nextId = 1;
    nextNationHue = 0;
    history.length = 0;
    simTime = 0;
    territory = new Int32Array(COLS * ROWS).fill(-1);
    territoryAccum = 0;
    selectedNationId = null;
    const toastContainer = document.getElementById('civToastContainer');
    if (toastContainer) toastContainer.innerHTML = '';

    // scatter starting population on livable land, away from ocean/mountain
    let placed = 0, guard = 0;
    while (placed < 140 && guard < 8000) {
      guard++;
      const x = rrandInt(0, COLS - 1), y = rrandInt(0, ROWS - 1);
      const t = cellType[idx(x, y)];
      if (t !== T_PLAINS && t !== T_COAST) continue;
      addPerson(x + 0.5, y + 0.5, randomRace());
      placed++;
    }
  }

  function addPerson(x, y, race) {
    people.push({
      id: nextId++, x, y, race: race === undefined ? randomRace() : race,
      vx: rrand(-1, 1), vy: rrand(-1, 1),
      energy: rrand(4, 7), age: 0, cooldown: rrand(0, 6),
    });
  }

  // ---------- SPATIAL BUCKETS (for settlement founding density checks) ----
  const BUCKET_SIZE = 6;
  function bucketsFor(list) {
    const m = new Map();
    for (let k = 0; k < list.length; k++) {
      const p = list[k];
      const key = Math.floor(p.x / BUCKET_SIZE) + ',' + Math.floor(p.y / BUCKET_SIZE);
      let arr = m.get(key);
      if (!arr) { arr = []; m.set(key, arr); }
      arr.push(k);
    }
    return m;
  }
  function countNear(buckets, list, x, y, radius) {
    const br = Math.ceil(radius / BUCKET_SIZE);
    const bx0 = Math.floor(x / BUCKET_SIZE), by0 = Math.floor(y / BUCKET_SIZE);
    let n = 0;
    for (let by = by0 - br; by <= by0 + br; by++) {
      for (let bx = bx0 - br; bx <= bx0 + br; bx++) {
        const arr = buckets.get(bx + ',' + by);
        if (!arr) continue;
        for (const k of arr) {
          const p = list[k];
          if (Math.hypot(p.x - x, p.y - y) <= radius) n++;
        }
      }
    }
    return n;
  }

  // ---------- NATIONS -------------------------------------------------
  const NATION_JOIN_RADIUS = 34;
  function foundNation(x, y) {
    const ideology = pick(IDEOLOGIES);
    const culture = pickCulture();
    const dynasty = genFamilyName(culture);
    const colorInfo = nextNationColor();
    const nation = {
      id: nextId++,
      name: genNationName(culture),
      color: colorInfo.css,
      rgb: colorInfo.rgb,
      ideology,
      culture,
      dynasty,
      leader: genLeader(dynasty, culture),
      religion: genReligionName(),
      faith: rrand(0.05, 0.15),
      age: 0,
      settlementIds: [],
      civLevel: 1,
      totalPopulation: 0,
      raceTotals: new Array(RACES.length).fill(0),
    };
    nations.push(nation);
    pushSpeech(nation, '건국 선언', 'founding');
    showGlobalNotification(`🎉 ${nation.name}이(가) 건국되었습니다.`, 'birth');
    return nation;
  }
  function nearestNation(x, y) {
    let best = null, bestD = NATION_JOIN_RADIUS;
    for (const nation of nations) {
      for (const sid of nation.settlementIds) {
        const s = settlements.find((s) => s.id === sid);
        if (!s) continue;
        const d = Math.hypot(s.x - x, s.y - y);
        if (d < bestD) { bestD = d; best = nation; }
      }
    }
    return best;
  }

  // ---------- TERRITORY ---------------------------------------------------
  // Each settlement claims land within a reach that grows with its
  // population (capitals get a bonus); every land cell is assigned to
  // whichever settlement's claim scores highest there, and inherits that
  // settlement's nation. Ocean is never claimed.
  function recomputeTerritory() {
    territory.fill(-1);
    if (!settlements.length) return;
    for (let y = 0; y < ROWS; y++) {
      for (let x = 0; x < COLS; x++) {
        const i = idx(x, y);
        if (cellType[i] === T_OCEAN) continue;
        const cx = x + 0.5, cy = y + 0.5;
        let bestNationId = -1, bestScore = -Infinity;
        for (const s of settlements) {
          const reach = 10 + Math.sqrt(s.population) * 1.6 + (s.isCapital ? 8 : 0);
          const d = Math.hypot(s.x - cx, s.y - cy);
          if (d > reach) continue;
          const score = reach - d;
          if (score > bestScore) { bestScore = score; bestNationId = s.nationId; }
        }
        territory[i] = bestNationId;
      }
    }
  }

  // ---------- SETTLEMENTS -----------------------------------------------
  const SETTLE_DENSITY = 5;
  const SETTLE_RADIUS = 3;
  const SETTLE_MIN_GAP = 16;
  const CITY_POP = 150;

  function trySettleFrom(buckets) {
    for (let k = 0; k < people.length; k++) {
      const p = people[k];
      const t = cellType[idx(Math.floor(p.x), Math.floor(p.y))];
      if (t !== T_PLAINS && t !== T_COAST && t !== T_HILLS) continue;
      const density = countNear(buckets, people, p.x, p.y, SETTLE_RADIUS);
      if (density < SETTLE_DENSITY) continue;
      let tooClose = false;
      for (const s of settlements) {
        if (Math.hypot(s.x - p.x, s.y - p.y) < SETTLE_MIN_GAP) { tooClose = true; break; }
      }
      if (tooClose) continue;

      // found it: absorb nearby free people into the new settlement's population
      let absorbed = 0;
      const raceCounts = new Array(RACES.length).fill(0);
      const remaining = [];
      for (const person of people) {
        if (Math.hypot(person.x - p.x, person.y - p.y) <= SETTLE_RADIUS && absorbed < 12) {
          absorbed++;
          raceCounts[person.race]++;
        } else remaining.push(person);
      }
      people = remaining;
      if (absorbed === 0) raceCounts[p.race]++;

      let nation = nearestNation(p.x, p.y);
      let isCapital = false;
      if (!nation) { nation = foundNation(p.x, p.y); isCapital = true; }

      const population = Math.max(6, absorbed);
      const raceSum = raceCounts.reduce((a, b) => a + b, 0) || 1;
      let domRaceIdx = 0;
      for (let ri = 1; ri < raceCounts.length; ri++) if (raceCounts[ri] > raceCounts[domRaceIdx]) domRaceIdx = ri;
      const settlement = {
        id: nextId++, x: p.x, y: p.y,
        name: genPersonName(nation.culture) + pick(['성', '촌', '항', '진']),
        nationId: nation.id,
        population,
        raceComposition: raceCounts.map((c) => (c / raceSum) * population),
        isCity: false, isCapital,
        ideology: nation.ideology,
        leaderName: isCapital ? nation.leader.name : genPersonName(nation.culture),
        leaderRace: domRaceIdx,
        founded: simTime,
      };
      settlements.push(settlement);
      nation.settlementIds.push(settlement.id);
      return true; // one new settlement per tick is plenty
    }
    return false;
  }

  // Regional ideological drift: a settlement can slowly diverge from its
  // nation's official ideology. Weaker national cohesion (lower faith)
  // makes drift more likely, and the region is more likely to drift toward
  // an ideology it's already philosophically close to.
  function driftSettlementIdeology(s, nation, dt) {
    if (!nation || !s.ideology) return;
    const driftChance = 0.000015 * dt * 20 * (1.4 - nation.faith);
    if (rng() >= driftChance) return;
    const affinities = IDEOLOGY_AFFINITY[s.ideology] || {};
    const candidates = IDEOLOGIES.filter((id) => id !== s.ideology);
    const weights = candidates.map((id) => Math.max(0.2, 5 + (affinities[id] || 0)));
    const total = weights.reduce((a, b) => a + b, 0);
    let r = rng() * total;
    let chosen = candidates[candidates.length - 1];
    for (let i = 0; i < candidates.length; i++) {
      r -= weights[i];
      if (r <= 0) { chosen = candidates[i]; break; }
    }
    s.ideology = chosen;
  }

  // Leaders are actual people, not a fixed icon: each wanders on a leash
  // around their own settlement (never leaving it far behind, never
  // crossing onto ocean), with an occasional new wander direction and a
  // gentle pull back home if they've strayed too far.
  const LEADER_LEASH = 2.4;
  function tickLeaders(dt) {
    for (const s of settlements) {
      if (s.leaderX === undefined) {
        s.leaderX = s.x; s.leaderY = s.y;
        s.leaderVx = rrand(-0.5, 0.5); s.leaderVy = rrand(-0.5, 0.5);
      }
      const dxHome = s.x - s.leaderX, dyHome = s.y - s.leaderY;
      const distHome = Math.hypot(dxHome, dyHome);
      if (distHome > LEADER_LEASH) {
        s.leaderVx = lerp(s.leaderVx, (dxHome / distHome) * 0.9, 0.5);
        s.leaderVy = lerp(s.leaderVy, (dyHome / distHome) * 0.9, 0.5);
      } else if (rng() < 0.015) {
        s.leaderVx = rrand(-0.6, 0.6);
        s.leaderVy = rrand(-0.6, 0.6);
      }
      const nx = s.leaderX + s.leaderVx * dt, ny = s.leaderY + s.leaderVy * dt;
      const cx = clamp(Math.floor(nx), 0, COLS - 1), cy = clamp(Math.floor(ny), 0, ROWS - 1);
      if (cellType[idx(cx, cy)] === T_OCEAN) {
        s.leaderVx *= -1; s.leaderVy *= -1;
      } else {
        s.leaderX = nx; s.leaderY = ny;
      }
    }
  }

  function tickSettlements(dt) {
    for (const s of settlements) {
      const nation = nations.find((n) => n.id === s.nationId);
      if (!s.isCapital) driftSettlementIdeology(s, nation, dt);
      const cx = Math.floor(s.x), cy = Math.floor(s.y);
      let avgRes = 0, n = 0;
      for (let dy = -2; dy <= 2; dy++) {
        for (let dx = -2; dx <= 2; dx++) {
          const x = cx + dx, y = cy + dy;
          if (!inBounds(x, y)) continue;
          const t = cellType[idx(x, y)];
          if (t === T_PLAINS || t === T_COAST || t === T_HILLS) { avgRes += resource[idx(x, y)]; n++; }
        }
      }
      avgRes = n ? avgRes / n : 0.1;

      const growth = (avgRes - 0.32) * params.growthRate * 0.02; // nerfed relative to ecosystem breeding rates
      const growthFactor = Math.max(0, 1 + growth * dt);
      s.population = Math.max(0, s.population * growthFactor);
      if (s.raceComposition) {
        for (let ri = 0; ri < s.raceComposition.length; ri++) s.raceComposition[ri] *= growthFactor;
      }
      // settlements consume a little local resource as they grow
      for (let dy = -2; dy <= 2; dy++) {
        for (let dx = -2; dx <= 2; dx++) {
          const x = cx + dx, y = cy + dy;
          if (!inBounds(x, y)) continue;
          const i = idx(x, y);
          const t = cellType[i];
          if (t === T_PLAINS || t === T_COAST || t === T_HILLS) {
            resource[i] = clamp(resource[i] - s.population * 0.000006 * dt, 0, 1);
          }
        }
      }
      if (!s.isCity && s.population >= CITY_POP) s.isCity = true;

      // rare emigration: a small group breaks off to found a settlement elsewhere
      if (s.population > 40 && rng() < 0.00025 * dt * 20) {
        const ang = rrand(0, Math.PI * 2);
        const dist = rrand(6, 16);
        const nx = clamp(s.x + Math.cos(ang) * dist, 1, COLS - 2);
        const ny = clamp(s.y + Math.sin(ang) * dist, 1, ROWS - 2);
        if (cellType[idx(Math.floor(nx), Math.floor(ny))] !== T_OCEAN) {
          for (let i = 0; i < 4; i++) {
            addPerson(nx + rrand(-1, 1), ny + rrand(-1, 1), pickRaceFromComposition(s.raceComposition));
          }
          const oldPop = s.population;
          s.population = Math.max(4, s.population - 4);
          if (s.raceComposition && oldPop > 0) {
            const ratio = s.population / oldPop;
            for (let ri = 0; ri < s.raceComposition.length; ri++) s.raceComposition[ri] *= ratio;
          }
        }
      }
    }
    // starved settlements slowly disappear
    settlements = settlements.filter((s) => {
      if (s.population > 1) return true;
      const nation = nations.find((n) => n.id === s.nationId);
      if (nation) nation.settlementIds = nation.settlementIds.filter((id) => id !== s.id);
      return false;
    });
  }

  function tickNations(dt) {
    for (const nation of nations) {
      nation.age += dt;
      const nationSettlements = nation.settlementIds.map((sid) => settlements.find((s) => s.id === sid)).filter(Boolean);

      // If the capital was destroyed (drowned, starved out, or otherwise
      // lost) but the nation still holds other land, its remaining
      // settlements hold an internal council and elect a new capital --
      // the most populous survivor -- rather than the nation quietly
      // going capital-less.
      if (nationSettlements.length && !nationSettlements.some((s) => s.isCapital)) {
        const newCapital = nationSettlements.reduce((best, s) => (s.population > best.population ? s : best));
        newCapital.isCapital = true;
        nation.leader = genLeader(nation.dynasty, nation.culture);
        pushSpeech(nation, '수도 재건', 'capital_relocated', { settlementName: newCapital.name });
        showGlobalNotification(`🏛️ ${nation.name}: 수도 함락, ${newCapital.name}(으)로 천도.`, 'power');
      }

      let pop = 0;
      const raceTotals = new Array(RACES.length).fill(0);
      for (const s of nationSettlements) {
        pop += s.population;
        if (s.raceComposition) {
          for (let ri = 0; ri < RACES.length; ri++) raceTotals[ri] += s.raceComposition[ri] || 0;
        }
      }
      nation.totalPopulation = pop;
      nation.raceTotals = raceTotals;
      nation.civLevel = clamp(1 + Math.floor(pop / 180) + Math.floor(nation.age / 260) + Math.floor(nation.settlementIds.length / 3), 1, 5);
      nation.faith = clamp(nation.faith + 0.0004 * dt * (1 + nation.civLevel * 0.2), 0, 1);

      // Leader succession: usually stays within the ruling family (a new
      // name, same dynasty); rarely a rival family seizes power instead,
      // which can also shift the nation's ideology.
      if (simTime - nation.leader.termStart > nation.leader.termLength) {
        const revolution = rng() < 0.12;
        const oldDynasty = nation.leader.dynasty;
        const culture = revolution ? pickCulture() : nation.culture;
        const dynasty = revolution ? genFamilyName(culture) : nation.leader.dynasty;
        if (revolution) {
          nation.dynasty = dynasty;
          nation.culture = culture;
          nation.ideology = pick(IDEOLOGIES);
        }
        nation.leader = genLeader(dynasty, culture);
        pushSpeech(nation, revolution ? '왕조 교체' : '지도자 승계', 'succession');
        if (revolution) {
          showGlobalNotification(`⚔️ ${nation.name}: ${oldDynasty} 몰락, ${dynasty} 집권.`, 'power');
        }
      }
    }
    const collapsed = nations.filter((n) => n.settlementIds.length === 0);
    for (const n of collapsed) {
      showGlobalNotification(`⚰️ ${n.name}이(가) 멸망했습니다. (${n.dynasty} 가문 몰락)`, 'fall');
    }
    nations = nations.filter((n) => n.settlementIds.length > 0);
  }

  // ---------- WAR & PLUNDER -------------------------------------------
  const RAID_RANGE = 22;
  const RAID_CHANCE = 0.25; // expected raids per nearby settlement pair per simulated second, while at war
  function performRaid(sa, na, sb, nb) {
    const totalPop = sa.population + sb.population || 1;
    const aIsAttacker = rng() < sa.population / totalPop; // the larger side has the military edge
    const attacker = aIsAttacker ? sa : sb, attackerNation = aIsAttacker ? na : nb;
    const defender = aIsAttacker ? sb : sa, defenderNation = aIsAttacker ? nb : na;

    const plunderFrac = rrand(0.12, 0.28);
    const plundered = defender.population * plunderFrac;
    defender.population = Math.max(1, defender.population - plundered);
    if (defender.raceComposition) {
      for (let ri = 0; ri < defender.raceComposition.length; ri++) defender.raceComposition[ri] *= (1 - plunderFrac);
    }
    const spoils = plundered * 0.35; // attrition -- raiders bring home less than what was taken
    attacker.population += spoils;
    if (attacker.raceComposition) {
      const total = attacker.raceComposition.reduce((a, b) => a + b, 0) || 1;
      for (let ri = 0; ri < attacker.raceComposition.length; ri++) {
        attacker.raceComposition[ri] += (attacker.raceComposition[ri] / total) * spoils;
      }
    }
    // the raid also loots and burns local resources around the defender
    const cx = Math.floor(defender.x), cy = Math.floor(defender.y);
    for (let dy = -2; dy <= 2; dy++) {
      for (let dx = -2; dx <= 2; dx++) {
        const x = cx + dx, y = cy + dy;
        if (!inBounds(x, y)) continue;
        const i = idx(x, y);
        resource[i] = clamp(resource[i] * 0.5, 0, 1);
      }
    }

    // a decisive raid can outright capture a non-capital settlement --
    // territory actually changes hands, not just population/resources
    const decisive = attacker.population > defender.population * 1.4;
    if (decisive && !defender.isCapital && rng() < 0.18) {
      defenderNation.settlementIds = defenderNation.settlementIds.filter((id) => id !== defender.id);
      attackerNation.settlementIds.push(defender.id);
      defender.nationId = attackerNation.id;
      defender.ideology = attackerNation.ideology; // reorganized under the conqueror
      recomputeTerritory();
      pushSpeech(attackerNation, '영토 점령', 'settlement_captured', { settlementName: defender.name });
    }
  }
  // As a nation's technology (civLevel) advances, war escalates beyond
  // local raids: from civLevel 4 it can air-strike any enemy settlement
  // anywhere on the map, and from civLevel 5 (근대) it can use a nuclear
  // strike -- rare, catastrophic, and felt by the whole world's opinion of
  // whoever used it, not just the two nations at war.
  function scorchAround(cx0, cy0, radius, keepFrac) {
    const cx = Math.floor(cx0), cy = Math.floor(cy0);
    for (let dy = -radius; dy <= radius; dy++) {
      for (let dx = -radius; dx <= radius; dx++) {
        if (dx * dx + dy * dy > radius * radius) continue;
        const x = cx + dx, y = cy + dy;
        if (!inBounds(x, y)) continue;
        const i = idx(x, y);
        resource[i] = clamp(resource[i] * keepFrac, 0, 1);
      }
    }
  }
  function performAirStrike(attackerNation, target) {
    const dmgFrac = rrand(0.18, 0.35);
    target.population = Math.max(1, target.population * (1 - dmgFrac));
    if (target.raceComposition) {
      for (let ri = 0; ri < target.raceComposition.length; ri++) target.raceComposition[ri] *= (1 - dmgFrac);
    }
    scorchAround(target.x, target.y, 3, 0.3);
    pushSpeech(attackerNation, '공습 감행', 'airstrike', { settlementName: target.name });
  }
  function performNuclearStrike(attackerNation, defenderNation, target) {
    const dmgFrac = rrand(0.65, 0.9);
    target.population = Math.max(1, target.population * (1 - dmgFrac));
    if (target.raceComposition) {
      for (let ri = 0; ri < target.raceComposition.length; ri++) target.raceComposition[ri] *= (1 - dmgFrac);
    }
    scorchAround(target.x, target.y, 6, 0.03);
    pushSpeech(attackerNation, '핵무기 사용', 'nuclear_strike', { settlementName: target.name });
    showGlobalNotification(`💥 ${attackerNation.name}이(가) ${target.name}(${defenderNation.name})에 핵무기를 사용했습니다.`, 'nuke');
    // the world recoils: relations with the victim bottom out, and every
    // other nation grows warier of the attacker, not just the target
    relations.set(relationKey(attackerNation.id, defenderNation.id), -100);
    for (const other of nations) {
      if (other.id === attackerNation.id || other.id === defenderNation.id) continue;
      const k = relationKey(attackerNation.id, other.id);
      const cur = relations.has(k) ? relations.get(k) : 0;
      relations.set(k, clamp(cur - 25, -100, 100));
    }
  }
  const AIRSTRIKE_CIV_LEVEL = 4;
  const NUKE_CIV_LEVEL = 5;
  function considerAdvancedStrike(attackerNation, defenderNation) {
    const targets = settlements.filter((s) => s.nationId === defenderNation.id);
    if (!targets.length) return;
    if (attackerNation.civLevel >= NUKE_CIV_LEVEL && rng() < 0.00035 * WAR_CHECK_INTERVAL) {
      performNuclearStrike(attackerNation, defenderNation, pick(targets));
      return;
    }
    if (attackerNation.civLevel >= AIRSTRIKE_CIV_LEVEL && rng() < 0.006 * WAR_CHECK_INTERVAL) {
      performAirStrike(attackerNation, pick(targets));
    }
  }
  function tickWarPlunder() {
    for (let i = 0; i < nations.length; i++) {
      for (let j = i + 1; j < nations.length; j++) {
        const a = nations[i], b = nations[j];
        if (!isAtWar(a.id, b.id)) continue;
        considerAdvancedStrike(a, b);
        considerAdvancedStrike(b, a);
        const aSettlements = settlements.filter((s) => s.nationId === a.id);
        const bSettlements = settlements.filter((s) => s.nationId === b.id);
        for (const sa of aSettlements) {
          for (const sb of bSettlements) {
            if (Math.hypot(sa.x - sb.x, sa.y - sb.y) > RAID_RANGE) continue;
            if (rng() < RAID_CHANCE * WAR_CHECK_INTERVAL) performRaid(sa, a, sb, b);
          }
        }
      }
    }
  }

  // ---------- PEOPLE (free-roaming) ---------------------------------------
  function cellAt(x, y) { return idx(clamp(Math.floor(x), 0, COLS - 1), clamp(Math.floor(y), 0, ROWS - 1)); }

  function tryMovePerson(p, dt) {
    const nx = p.x + p.vx * dt, ny = p.y + p.vy * dt;
    if (nx < 0 || nx >= COLS || ny < 0 || ny >= ROWS) { p.vx *= -1; p.vy *= -1; return; }
    const t = cellType[cellAt(nx, ny)];
    if (t === T_OCEAN) { p.vx *= -1; p.vy *= -1; return; }
    p.x = nx; p.y = ny;
  }

  function updatePerson(p, dt) {
    p.energy -= 0.32 * dt;
    p.age += dt;
    p.cooldown = Math.max(0, p.cooldown - dt);
    const i = cellAt(p.x, p.y);
    const t = cellType[i];

    if (t === T_PLAINS || t === T_COAST || t === T_HILLS) {
      if (resource[i] > 0.04) {
        const eat = Math.min(resource[i], 0.28 * dt);
        resource[i] -= eat;
        p.energy += eat * 3.0;
      }
    }

    // seek nearby resource-rich land, gentle wander otherwise
    let bestScore = -1, bestX = p.x, bestY = p.y;
    for (let s = 0; s < 4; s++) {
      const sx = clamp(p.x + rrand(-4, 4), 0, COLS - 1);
      const sy = clamp(p.y + rrand(-4, 4), 0, ROWS - 1);
      const si = cellAt(sx, sy);
      const st = cellType[si];
      if (st === T_OCEAN) continue;
      const score = (st === T_PLAINS || st === T_COAST ? resource[si] : 0.05) + rng() * 0.1;
      if (score > bestScore) { bestScore = score; bestX = sx; bestY = sy; }
    }
    const dx = bestX - p.x, dy = bestY - p.y;
    const len = Math.hypot(dx, dy) || 1;
    p.vx = lerp(p.vx, (dx / len) * 1.1, 0.35);
    p.vy = lerp(p.vy, (dy / len) * 1.1, 0.35);
    tryMovePerson(p, dt);

    // reproduction, heavily nerfed vs the ecosystem sim's animals
    if (p.energy > 9 && p.cooldown <= 0) {
      p.energy -= 6;
      p.cooldown = 30;
      addPerson(clamp(p.x + rrand(-1, 1), 0, COLS - 1), clamp(p.y + rrand(-1, 1), 0, ROWS - 1), p.race);
    }
    return p.energy > 0;
  }

  function tickPeople(dt) {
    const next = [];
    for (const p of people) if (updatePerson(p, dt)) next.push(p);
    people = next;

    const buckets = bucketsFor(people);
    trySettleFrom(buckets);
  }

  // ---------- MAIN TICK -----------------------------------------------
  function tickTerrain(dt) {
    for (let i = 0; i < cellType.length; i++) {
      if ((cellType[i] === T_PLAINS || cellType[i] === T_COAST || cellType[i] === T_HILLS) && resource[i] < 1) {
        resource[i] = clamp(resource[i] + params.resourceRegrow * dt, 0, 1);
      }
    }
  }

  function tick() {
    tickTerrain(TICK_DT);
    tickPeople(TICK_DT);
    tickSettlements(TICK_DT);
    tickLeaders(TICK_DT);
    tickNations(TICK_DT);
    tickDiplomacy(TICK_DT);
    simTime += TICK_DT;

    territoryAccum += TICK_DT;
    if (territoryAccum >= TERRITORY_INTERVAL) {
      territoryAccum = 0;
      recomputeTerritory();
    }

    warAccum += TICK_DT;
    if (warAccum >= WAR_CHECK_INTERVAL) {
      warAccum = 0;
      tickWarPlunder();
    }

    sampleAccum += TICK_DT;
    if (sampleAccum >= SAMPLE_INTERVAL) {
      sampleAccum = 0;
      sampleHistory();
    }
  }

  function sampleHistory() {
    let totalPop = people.length;
    for (const s of settlements) totalPop += s.population;
    const avgCiv = nations.length ? nations.reduce((a, n) => a + n.civLevel, 0) / nations.length : 0;
    history.push({ pop: totalPop, settlements: settlements.length, nations: nations.length, civ: avgCiv });
    if (history.length > HISTORY_MAX) history.shift();
    updateCounts(totalPop, settlements.length, nations.length);
    updateNationList();
    if (diplomacyOpen && activeDiploTab === 'diplomacy') renderDiplomacyPanel();
  }

  // ---------- RENDERING -----------------------------------------------
  const terrainCanvas = document.getElementById('civTerrainCanvas');
  const tctx = terrainCanvas.getContext('2d', { alpha: false });
  const entityCanvas = document.getElementById('civEntityCanvas');
  const ectx = entityCanvas.getContext('2d');
  const canvasWrap = document.getElementById('civCanvasWrap');

  terrainCanvas.width = COLS;
  terrainCanvas.height = ROWS;
  const terrainImage = tctx.createImageData(COLS, ROWS);

  const COL = {
    oceanDeep: [8, 26, 56], oceanShallow: [22, 60, 110], coast: [196, 178, 118],
    plainsLow: [58, 92, 40], plainsHigh: [104, 158, 64],
    hills: [107, 96, 58], mountain: [110, 105, 100], snow: [232, 236, 240],
    river: [46, 110, 190],
  };

  function renderTerrain() {
    const data = terrainImage.data;
    const nationRgbById = new Map();
    for (const n of nations) nationRgbById.set(n.id, n.rgb);
    const TERRITORY_TINT = 0.32;
    for (let i = 0; i < cellType.length; i++) {
      const p = i * 4;
      const t = cellType[i];
      const e = elevation[i];
      const tex = (texNoise[i] - 0.5) * 14;
      let r, g, b;
      if (isRiver[i] && t !== T_OCEAN) {
        r = COL.river[0]; g = COL.river[1]; b = COL.river[2];
      } else if (t === T_OCEAN) {
        const m = clamp((e / T_OCEAN_E), 0, 1);
        r = lerp(COL.oceanDeep[0], COL.oceanShallow[0], m);
        g = lerp(COL.oceanDeep[1], COL.oceanShallow[1], m);
        b = lerp(COL.oceanDeep[2], COL.oceanShallow[2], m);
      } else if (t === T_COAST) {
        r = COL.coast[0] + tex; g = COL.coast[1] + tex; b = COL.coast[2] + tex * 0.5;
      } else if (t === T_PLAINS) {
        const m = clamp(resource[i], 0, 1);
        r = lerp(COL.plainsLow[0], COL.plainsHigh[0], m) + tex;
        g = lerp(COL.plainsLow[1], COL.plainsHigh[1], m) + tex;
        b = lerp(COL.plainsLow[2], COL.plainsHigh[2], m) + tex * 0.4;
      } else if (t === T_HILLS) {
        r = COL.hills[0] + tex; g = COL.hills[1] + tex; b = COL.hills[2] + tex * 0.5;
      } else if (t === T_MOUNTAIN) {
        r = COL.mountain[0] + tex; g = COL.mountain[1] + tex; b = COL.mountain[2] + tex;
      } else {
        r = COL.snow[0]; g = COL.snow[1]; b = COL.snow[2];
      }
      if (territory[i] >= 0) {
        const nrgb = nationRgbById.get(territory[i]);
        if (nrgb) {
          r = r + (nrgb[0] - r) * TERRITORY_TINT;
          g = g + (nrgb[1] - g) * TERRITORY_TINT;
          b = b + (nrgb[2] - b) * TERRITORY_TINT;
        }
      }
      data[p] = clamp(r, 0, 255);
      data[p + 1] = clamp(g, 0, 255);
      data[p + 2] = clamp(b, 0, 255);
      data[p + 3] = 255;
    }
    tctx.putImageData(terrainImage, 0, 0);
  }

  // ---------- LEADER HATS -------------------------------------------------
  // Every settlement has a leader (the capital's is the nation's head of
  // state; every other settlement has a regional head) whose title comes
  // from the nation's ideology (LEADER_TITLE / REGIONAL_TITLE). Each
  // ideology gets its own hat silhouette, and within an ideology the
  // national leader's hat is drawn larger and in gold while a regional
  // leader's is smaller and in silver -- so every one of the ten titles
  // reads as visually distinct headwear.
  function drawCrown(ctx, cx, cy, w, h, color) {
    ctx.fillStyle = color;
    ctx.beginPath();
    ctx.moveTo(cx - w / 2, cy + h / 2);
    ctx.lineTo(cx - w / 2, cy - h * 0.05);
    ctx.lineTo(cx - w / 3, cy - h / 2);
    ctx.lineTo(cx - w / 6, cy - h * 0.1);
    ctx.lineTo(cx, cy - h * 0.55);
    ctx.lineTo(cx + w / 6, cy - h * 0.1);
    ctx.lineTo(cx + w / 3, cy - h / 2);
    ctx.lineTo(cx + w / 2, cy - h * 0.05);
    ctx.lineTo(cx + w / 2, cy + h / 2);
    ctx.closePath();
    ctx.fill();
  }
  function drawMitre(ctx, cx, cy, w, h, color) {
    ctx.fillStyle = color;
    ctx.beginPath();
    ctx.moveTo(cx - w / 2, cy + h / 2);
    ctx.lineTo(cx - w / 2, cy - h * 0.05);
    ctx.quadraticCurveTo(cx - w / 4, cy - h * 0.55, cx, cy - h * 0.6);
    ctx.quadraticCurveTo(cx + w / 4, cy - h * 0.55, cx + w / 2, cy - h * 0.05);
    ctx.lineTo(cx + w / 2, cy + h / 2);
    ctx.closePath();
    ctx.fill();
  }
  function drawTopHat(ctx, cx, cy, w, h, color) {
    ctx.fillStyle = color;
    ctx.fillRect(cx - w / 2, cy + h * 0.28, w, h * 0.16);
    ctx.fillRect(cx - w * 0.32, cy - h / 2, w * 0.64, h * 0.8);
  }
  function drawPeakedCap(ctx, cx, cy, w, h, color) {
    ctx.fillStyle = color;
    ctx.beginPath();
    ctx.ellipse(cx, cy - h * 0.08, w * 0.42, h * 0.42, 0, Math.PI, 0, true);
    ctx.fill();
    ctx.fillRect(cx - w / 2, cy - h * 0.1, w, h * 0.14);
    ctx.beginPath();
    ctx.ellipse(cx + w * 0.16, cy + h * 0.1, w * 0.4, h * 0.14, 0, 0, Math.PI);
    ctx.fill();
  }
  function drawHeaddress(ctx, cx, cy, w, h, color) {
    ctx.fillStyle = color;
    ctx.fillRect(cx - w / 2, cy + h * 0.22, w, h * 0.16);
    const n = 5;
    for (let i = 0; i < n; i++) {
      const t = i / (n - 1);
      const fx = cx - w / 2 + t * w;
      const fh = h * (0.55 + 0.35 * Math.sin(t * Math.PI));
      ctx.beginPath();
      ctx.moveTo(fx - w * 0.06, cy + h * 0.22);
      ctx.lineTo(fx, cy + h * 0.22 - fh);
      ctx.lineTo(fx + w * 0.06, cy + h * 0.22);
      ctx.closePath();
      ctx.fill();
    }
  }
  const HAT_BY_IDEOLOGY = {
    군주제: drawCrown, 신정: drawMitre, 공화정: drawTopHat,
    전체주의: drawPeakedCap, 부족연합: drawHeaddress,
  };
  function drawLeaderHat(ctx, cx, topY, ideology, isNational) {
    const draw = HAT_BY_IDEOLOGY[ideology];
    if (!draw) return;
    const scale = isNational ? 1 : 0.62;
    const w = 11 * scale, h = 9.5 * scale;
    const color = isNational ? '#FFCC11' : '#E8E4D8';
    ctx.save();
    ctx.strokeStyle = 'rgba(0,0,0,0.5)';
    ctx.lineWidth = 0.6;
    draw(ctx, cx, topY - h / 2, w, h, color);
    ctx.restore();
  }

  // Draws one walk-cycle frame of a race's sprite, feet-anchored at (px,py).
  // Returns true if it actually drew an image (false = still loading).
  function drawPersonSprite(ctx, px, py, race, frameIdx, heightPx, flip) {
    const img = race.images[frameIdx];
    if (!img || !img.complete || !img.naturalWidth) return false;
    const w = heightPx * (img.naturalWidth / img.naturalHeight);
    ctx.save();
    ctx.translate(px, py);
    if (flip) ctx.scale(-1, 1); // sprites face left by default
    ctx.drawImage(img, -w / 2, -heightPx, w, heightPx);
    ctx.restore();
    return true;
  }

  function renderEntities() {
    const w = entityCanvas.width, h = entityCanvas.height;
    ectx.clearRect(0, 0, w, h);
    const sx = w / COLS, sy = h / ROWS;
    const cellPx = Math.min(sx, sy);

    const WALK_FPS = 3.2; // walk-cycle frame swaps per second
    const spriteH = clamp(cellPx * 3, 6, 22); // ordinary wandering people
    ectx.fillStyle = '#f1e9d8';
    for (const p of people) {
      const race = RACES[p.race] || RACES[0];
      const frameIdx = Math.floor((simTime + p.id * 0.53) * WALK_FPS) % 2;
      const px = p.x * sx, py = p.y * sy;
      const drawn = drawPersonSprite(ectx, px, py, race, frameIdx, spriteH, p.vx > 0.02);
      if (!drawn) {
        // fallback dot while the sprite images are still loading
        ectx.beginPath();
        ectx.arc(px, py, Math.max(1, cellPx * 0.5), 0, Math.PI * 2);
        ectx.fill();
      }
    }

    // Leaders (national and regional heads) are people too, not just the
    // settlement marker: each settlement renders its leader as an actual
    // walking person -- wandering on a leash around their settlement (see
    // tickLeaders) -- larger than an ordinary wanderer, wearing their
    // title's hat. A selected nation (from the nation list) gets a pulsing
    // highlight ring on its settlement markers so its location is easy to
    // spot on the map.
    for (const s of settlements) {
      const nation = nations.find((n) => n.id === s.nationId);
      const cx = s.x * sx, cy = s.y * sy;
      const r = Math.max(2, cellPx * (s.isCity ? 1.7 : 1.1));
      ectx.fillStyle = nation ? nation.color : '#999';
      ectx.beginPath();
      ectx.arc(cx, cy, r, 0, Math.PI * 2);
      ectx.fill();
      ectx.strokeStyle = 'rgba(0,0,0,0.45)';
      ectx.lineWidth = 1;
      ectx.stroke();

      if (nation && selectedNationId === nation.id) {
        const pulse = r + 5 + 3 * Math.sin(simTime * 5);
        ectx.strokeStyle = '#FFCC11';
        ectx.lineWidth = 2;
        ectx.beginPath();
        ectx.arc(cx, cy, pulse, 0, Math.PI * 2);
        ectx.stroke();
      }

      const leaderRace = RACES[s.leaderRace] || RACES[0];
      const leaderH = Math.max(6, spriteH * 2.3);
      const lx = (s.leaderX === undefined ? s.x : s.leaderX) * sx;
      const ly = (s.leaderY === undefined ? s.y : s.leaderY) * sy;
      const frameIdx = Math.floor((simTime + s.id * 0.71) * WALK_FPS) % 2;
      const drawn = drawPersonSprite(ectx, lx, ly, leaderRace, frameIdx, leaderH, (s.leaderVx || 0) > 0.02);
      const hatTopY = ly - (drawn ? leaderH : r) - 1;
      if (nation) drawLeaderHat(ectx, lx, hatTopY, s.isCapital ? nation.ideology : (s.ideology || nation.ideology), s.isCapital);

      // the capital carries its nation's name -- anchored to the fixed
      // settlement position (not the wandering leader), so it stays put
      if (s.isCapital && nation) {
        const labelY = cy - r - leaderH - 20;
        const fontPx = Math.max(9, Math.min(15, cellPx * 1.6));
        ectx.font = `bold ${fontPx}px 'Nanum Myeongjo', Georgia, serif`;
        ectx.textAlign = 'center';
        ectx.textBaseline = 'bottom';
        ectx.fillStyle = 'rgba(0,0,0,0.65)';
        ectx.fillText(nation.name, cx + 1, labelY + 1);
        ectx.fillStyle = '#FFCC11';
        ectx.fillText(nation.name, cx, labelY);
      }
    }
  }

  // ---------- GRAPH -----------------------------------------------
  const graphCanvas = document.getElementById('civGraphCanvas');
  const gctx = graphCanvas.getContext('2d');

  function drawSeries(values, color, w, h, pad) {
    if (values.length < 2) return;
    let max = 0;
    for (const v of values) if (v > max) max = v;
    max = max * 1.15 || 1;
    gctx.strokeStyle = color;
    gctx.lineWidth = Math.max(1, h * 0.018);
    gctx.beginPath();
    for (let i = 0; i < values.length; i++) {
      const x = pad + (i / (HISTORY_MAX - 1)) * (w - pad * 2);
      const y = h - pad - (values[i] / max) * (h - pad * 2);
      if (i === 0) gctx.moveTo(x, y); else gctx.lineTo(x, y);
    }
    gctx.stroke();
  }
  function renderGraph() {
    const w = graphCanvas.width, h = graphCanvas.height;
    gctx.clearRect(0, 0, w, h);
    gctx.fillStyle = '#0c0a08';
    gctx.fillRect(0, 0, w, h);
    if (history.length < 2) return;
    const pad = h * 0.08;
    drawSeries(history.map((s) => s.pop), '#55BB44', w, h, pad);
    drawSeries(history.map((s) => s.settlements * 20), '#FF7E00', w, h, pad);
    drawSeries(history.map((s) => s.nations * 40), '#39C5BB', w, h, pad);
  }

  function updateCounts(pop, settlementCount, nationCount) {
    document.getElementById('civCntPeople').textContent = `🧍 ${Math.round(pop)}`;
    document.getElementById('civCntSettlements').textContent = `🏘️ ${settlementCount}`;
    document.getElementById('civCntNations').textContent = `🏳️ ${nationCount}`;
  }

  function updateNationList() {
    const list = document.getElementById('civNationList');
    if (!nations.length) {
      list.innerHTML = '<li class="civNationEmpty">아직 형성된 국가가 없습니다.</li>';
      return;
    }
    const sorted = [...nations].sort((a, b) => b.totalPopulation - a.totalPopulation);
    list.innerHTML = sorted.slice(0, 12).map((n) => {
      const tier = CIV_TIER_NAME[n.civLevel] || '';
      const L = n.leader;
      const raceTotals = n.raceTotals || [];
      let domIdx = 0, raceSum = 0;
      for (let ri = 0; ri < raceTotals.length; ri++) {
        raceSum += raceTotals[ri];
        if (raceTotals[ri] > (raceTotals[domIdx] || 0)) domIdx = ri;
      }
      const domRacePct = raceSum > 0 ? Math.round((raceTotals[domIdx] / raceSum) * 100) : 0;
      const domRaceName = RACES[domIdx] ? RACES[domIdx].name : '';
      const selected = n.id === selectedNationId ? ' selected' : '';
      return `<li class="civNationRow${selected}" data-nationid="${n.id}" title="클릭하면 지도에서 위치를 표시합니다">` +
        `<span class="civSwatch" style="background:${n.color}"></span>` +
        `<span><b>${n.name}</b> (${n.dynasty}) · ${LEADER_TITLE[n.ideology]} ${L.name} · ${n.ideology} · ${n.religion}(${Math.round(n.faith * 100)}%)` +
        `<br><span class="civMeta">${L.personality}·${L.philosophy}주의 지도자 · Lv.${n.civLevel} ${tier} · 인구 ${Math.round(n.totalPopulation)} · 정착지 ${n.settlementIds.length}` +
        (raceSum > 0 ? ` · 다수종족 ${domRaceName} ${domRacePct}%` : '') +
        `</span></span></li>`;
    }).join('');
  }

  // ---------- DIPLOMACY / REGIONAL IDEOLOGY WINDOW -------------------------
  let diplomacyOpen = false;
  let activeDiploTab = 'diplomacy';
  function renderSpeechPanel() {
    const body = document.getElementById('civSpeechBody');
    if (!speechLog.length) {
      body.innerHTML = '<div class="civDiploEmpty">아직 기록된 발언이 없습니다.</div>';
      return;
    }
    body.innerHTML = speechLog.map((e) => {
      return `<div class="civSpeechEntry"><div class="civSpeechHead"><span class="civSwatch" style="background:${e.nationColor}"></span>` +
        `<b>${e.nationName}</b> <span class="civMeta">${e.leaderName} · ${e.ideology} · ${e.eventLabel}</span></div>` +
        `<div class="civSpeechText">"${e.text}"</div></div>`;
    }).join('');
  }
  function setDiploTab(tab) {
    activeDiploTab = tab;
    document.querySelectorAll('.civModalTabBtn').forEach((b) => b.classList.toggle('active', b.dataset.diplotab === tab));
    document.getElementById('civDiplomacyBody').classList.toggle('hidden', tab !== 'diplomacy');
    document.getElementById('civSpeechBody').classList.toggle('hidden', tab !== 'speeches');
    if (tab === 'diplomacy') renderDiplomacyPanel(); else renderSpeechPanel();
  }
  function renderDiplomacyPanel() {
    const body = document.getElementById('civDiplomacyBody');
    if (!nations.length) {
      body.innerHTML = '<div class="civDiploEmpty">아직 형성된 국가가 없습니다.</div>';
      return;
    }
    const sorted = [...nations].sort((a, b) => b.totalPopulation - a.totalPopulation);
    body.innerHTML = sorted.map((n) => {
      const tier = CIV_TIER_NAME[n.civLevel] || '';
      const others = nations.filter((o) => o.id !== n.id);

      // at-a-glance relation counts before the per-nation detail chips
      const counts = { 'rel-ally': 0, 'rel-friendly': 0, 'rel-neutral': 0, 'rel-tense': 0, 'rel-war': 0 };
      for (const o of others) counts[REL_LABEL(getRelation(n.id, o.id)).cls]++;
      const LABELS = { 'rel-ally': '동맹', 'rel-friendly': '우호', 'rel-tense': '긴장', 'rel-war': '전쟁' };
      const summary = Object.keys(LABELS).map((cls) => counts[cls] ? `<span class="civRelChip ${cls}">${LABELS[cls]} ${counts[cls]}</span>` : '').join('')
        || '<span class="civDiploEmpty">이렇다 할 관계가 없습니다.</span>';
      const relRow = others.length
        ? others.map((o) => {
            const score = getRelation(n.id, o.id);
            const rel = REL_LABEL(score);
            return `<span class="civRelChip ${rel.cls}" title="${Math.round(score)}">${o.name} · ${rel.label}</span>`;
          }).join('')
        : '';

      const nationSettlements = settlements.filter((s) => s.nationId === n.id);
      const regionRows = nationSettlements.length
        ? nationSettlements.map((s) => {
            const ideologyText = s.isCapital ? n.ideology : (s.ideology || n.ideology);
            const title = s.isCapital ? LEADER_TITLE[n.ideology] : REGIONAL_TITLE[ideologyText];
            const diverged = !s.isCapital && ideologyText !== n.ideology;
            return `<tr class="${diverged ? 'civDiploDivergedRow' : ''}">` +
              `<td>${s.isCapital ? '👑 ' : ''}${s.name}${s.isCapital ? ' (수도)' : ''}</td>` +
              `<td>${title}</td><td>${s.leaderName}</td><td>${ideologyText}${diverged ? ' ⚠️' : ''}</td></tr>`;
          }).join('')
        : '<tr><td colspan="4" class="civDiploEmpty">정착지가 없습니다.</td></tr>';

      return `<div class="civDiploNation">` +
        `<div class="civDiploNationHead"><span class="civSwatch" style="background:${n.color}"></span><b>${n.name}</b> <span class="civMeta">(${n.dynasty})</span></div>` +
        `<dl class="civDiploStatGrid">` +
        `<dt>이념</dt><dd>${n.ideology}</dd>` +
        `<dt>지도자</dt><dd>${LEADER_TITLE[n.ideology]} ${n.leader.name} · ${n.leader.personality}·${n.leader.philosophy}주의</dd>` +
        `<dt>종교</dt><dd>${n.religion} (신앙 ${Math.round(n.faith * 100)}%)</dd>` +
        `<dt>문명</dt><dd>Lv.${n.civLevel} ${tier}</dd>` +
        `<dt>인구 · 정착지</dt><dd>${Math.round(n.totalPopulation)}명 · ${n.settlementIds.length}곳</dd>` +
        `<dt>문화</dt><dd>${n.culture ? n.culture.label : '-'}</dd>` +
        `</dl>` +
        `<div class="civDiploSection"><div class="civDiploSectionTitle">외교 관계</div>` +
        `<div class="civRelRow">${summary}</div>` +
        (relRow ? `<div class="civRelRow civRelRowDetail">${relRow}</div>` : '') +
        `</div>` +
        `<div class="civDiploSection"><div class="civDiploSectionTitle">지역별 사상</div>` +
        `<table class="civDiploTable"><thead><tr><th>지역</th><th>직위</th><th>지도자</th><th>사상</th></tr></thead><tbody>${regionRows}</tbody></table>` +
        `</div>` +
        `</div>`;
    }).join('');
  }
  function openDiplomacyPanel() {
    diplomacyOpen = true;
    document.getElementById('civDiplomacyOverlay').classList.remove('hidden');
    setDiploTab(activeDiploTab);
  }
  function closeDiplomacyPanel() {
    diplomacyOpen = false;
    document.getElementById('civDiplomacyOverlay').classList.add('hidden');
  }

  // ---------- VIEWPORT SIZING ----------------------------------------------
  function resizeEntityCanvas() {
    const rect = canvasWrap.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    entityCanvas.width = Math.max(1, Math.round(rect.width * dpr));
    entityCanvas.height = Math.max(1, Math.round(rect.height * dpr));
  }
  function resizeGraph() {
    const rect = graphCanvas.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    graphCanvas.width = Math.max(1, Math.round(rect.width * dpr));
    graphCanvas.height = Math.max(1, Math.round(rect.height * dpr));
  }
  window.addEventListener('resize', () => { resizeEntityCanvas(); resizeGraph(); });

  // ---------- INPUT / TOOLS -----------------------------------------------
  let pointerDown = false;
  function clientToGrid(clientX, clientY) {
    const rect = entityCanvas.getBoundingClientRect();
    return [((clientX - rect.left) / rect.width) * COLS, ((clientY - rect.top) / rect.height) * ROWS];
  }
  function applyTool(gx, gy) {
    if (currentTool === 'person') {
      addPerson(clamp(gx, 0, COLS - 1), clamp(gy, 0, ROWS - 1));
      return;
    }
    if (currentTool === 'settle') {
      const x = clamp(Math.floor(gx), 1, COLS - 2), y = clamp(Math.floor(gy), 1, ROWS - 2);
      if (cellType[idx(x, y)] === T_OCEAN) return;
      let nation = nearestNation(x, y);
      let isCapital = false;
      if (!nation) { nation = foundNation(x, y); isCapital = true; }
      const settlement = {
        id: nextId++, x: x + 0.5, y: y + 0.5,
        name: genPersonName(nation.culture) + pick(['성', '촌', '항', '진']),
        nationId: nation.id, population: 10,
        raceComposition: [5, 5],
        isCity: false, isCapital,
        ideology: nation.ideology,
        leaderName: isCapital ? nation.leader.name : genPersonName(nation.culture),
        leaderRace: randomRace(),
        founded: simTime,
      };
      settlements.push(settlement);
      nation.settlementIds.push(settlement.id);
      recomputeTerritory();
      return;
    }
    if (currentTool === 'erase') {
      const radius = params.brushSize;
      people = people.filter((p) => Math.hypot(p.x - gx, p.y - gy) > radius);
      settlements = settlements.filter((s) => {
        if (Math.hypot(s.x - gx, s.y - gy) > radius) return true;
        const nation = nations.find((n) => n.id === s.nationId);
        if (nation) nation.settlementIds = nation.settlementIds.filter((id) => id !== s.id);
        return false;
      });
      recomputeTerritory();
      return;
    }
    // terrain paint tools
    const radius = params.brushSize;
    const x0 = Math.max(0, Math.floor(gx - radius)), x1 = Math.min(COLS - 1, Math.ceil(gx + radius));
    const y0 = Math.max(0, Math.floor(gy - radius)), y1 = Math.min(ROWS - 1, Math.ceil(gy + radius));
    for (let y = y0; y <= y1; y++) {
      for (let x = x0; x <= x1; x++) {
        if (Math.hypot(x - gx, y - gy) > radius) continue;
        const i = idx(x, y);
        if (currentTool === 'ocean') { cellType[i] = T_OCEAN; isRiver[i] = 0; resource[i] = 0; }
        else if (currentTool === 'plains') { cellType[i] = T_PLAINS; resource[i] = 0.6; isRiver[i] = 0; }
        else if (currentTool === 'mountain') { cellType[i] = T_MOUNTAIN; resource[i] = 0; isRiver[i] = 0; }
      }
    }
    // if the land under a settlement was just drowned, the settlement goes with it
    if (currentTool === 'ocean') {
      const drownedIds = new Set(
        settlements.filter((s) => cellType[idx(Math.floor(s.x), Math.floor(s.y))] === T_OCEAN).map((s) => s.id)
      );
      if (drownedIds.size) {
        settlements = settlements.filter((s) => !drownedIds.has(s.id));
        for (const nation of nations) nation.settlementIds = nation.settlementIds.filter((id) => !drownedIds.has(id));
        recomputeTerritory();
      }
    }
  }
  function bindPointer() {
    entityCanvas.addEventListener('pointerdown', (ev) => {
      pointerDown = true;
      entityCanvas.setPointerCapture(ev.pointerId);
      const [gx, gy] = clientToGrid(ev.clientX, ev.clientY);
      applyTool(gx, gy);
    });
    entityCanvas.addEventListener('pointermove', (ev) => {
      if (!pointerDown) return;
      if (currentTool === 'person' || currentTool === 'settle') return; // one at a time
      const [gx, gy] = clientToGrid(ev.clientX, ev.clientY);
      applyTool(gx, gy);
    });
    window.addEventListener('pointerup', () => { pointerDown = false; });
    window.addEventListener('pointercancel', () => { pointerDown = false; });
  }

  function randomSeedString() {
    return Math.random().toString(36).slice(2, 8);
  }

  function bindUI() {
    // Event delegation: the nation list's <li> elements are replaced by
    // innerHTML on every refresh, so a per-item listener would be lost --
    // bind once on the container instead. Clicking the already-selected
    // nation again deselects it (same toggle-off pattern as the tools).
    document.getElementById('civNationList').addEventListener('click', (ev) => {
      const row = ev.target.closest('.civNationRow');
      if (!row) return;
      const id = Number(row.dataset.nationid);
      selectedNationId = selectedNationId === id ? null : id;
      updateNationList();
    });

    document.querySelectorAll('.civToolBtn').forEach((btn) => {
      btn.addEventListener('click', () => {
        const wasActive = btn.classList.contains('active');
        document.querySelectorAll('.civToolBtn').forEach((b) => b.classList.remove('active'));
        if (wasActive) { currentTool = null; return; } // click the active tool again to deselect it
        btn.classList.add('active');
        currentTool = btn.dataset.civtool;
      });
    });
    document.querySelectorAll('.civSpeedBtn').forEach((btn) => {
      btn.addEventListener('click', () => {
        document.querySelectorAll('.civSpeedBtn').forEach((b) => b.classList.remove('active'));
        btn.classList.add('active');
        speedMultiplier = Number(btn.dataset.speed);
      });
    });

    const seedInput = document.getElementById('civSeedInput');
    document.getElementById('civNewSeedBtn').addEventListener('click', () => {
      const seed = seedInput.value.trim() || randomSeedString();
      seedInput.value = seed;
      generateWorld(seed);
      closeDiplomacyPanel();
    });
    document.getElementById('civResetBtn').addEventListener('click', () => {
      generateWorld(currentSeed || randomSeedString());
      closeDiplomacyPanel();
    });

    document.getElementById('civDiplomacyBtn').addEventListener('click', () => {
      if (diplomacyOpen) closeDiplomacyPanel(); else openDiplomacyPanel();
    });
    document.getElementById('civDiplomacyCloseBtn').addEventListener('click', closeDiplomacyPanel);
    document.getElementById('civDiplomacyOverlay').addEventListener('click', (ev) => {
      if (ev.target.id === 'civDiplomacyOverlay') closeDiplomacyPanel();
    });
    document.querySelectorAll('.civModalTabBtn').forEach((btn) => {
      btn.addEventListener('click', () => setDiploTab(btn.dataset.diplotab));
    });

    const resourceSlider = document.getElementById('civResourceRateSlider');
    resourceSlider.addEventListener('input', () => { params.resourceRegrow = lerp(0.0008, 0.02, resourceSlider.value / 100); });
    params.resourceRegrow = lerp(0.0008, 0.02, resourceSlider.value / 100);

    const growthSlider = document.getElementById('civGrowthRateSlider');
    growthSlider.addEventListener('input', () => { params.growthRate = lerp(0.1, 3, growthSlider.value / 100); });
    params.growthRate = lerp(0.1, 3, growthSlider.value / 100);

    const brushSlider = document.getElementById('civBrushSizeSlider');
    brushSlider.addEventListener('input', () => { params.brushSize = Number(brushSlider.value); });
    params.brushSize = Number(brushSlider.value);
  }

  // ---------- MAIN LOOP (paused while this view is hidden) -----------------
  let running = false;

  function frame(now) {
    if (!running) return;
    if (!lastFrameTime) lastFrameTime = now;
    let dt = (now - lastFrameTime) / 1000;
    lastFrameTime = now;
    if (dt > 0.25) dt = 0.25;

    if (speedMultiplier > 0) {
      accumulator += dt * speedMultiplier;
      let n = 0;
      while (accumulator >= TICK_DT && n < MAX_TICKS_PER_FRAME) {
        tick();
        accumulator -= TICK_DT;
        n++;
      }
    }
    renderTerrain();
    renderEntities();
    renderGraph();
    requestAnimationFrame(frame);
  }

  window.pauseCiv = function () { running = false; };
  window.resumeCiv = function () {
    if (running) return;
    running = true;
    lastFrameTime = 0;
    resizeEntityCanvas();
    resizeGraph();
    requestAnimationFrame(frame);
  };

  // ---------- INIT -----------------------------------------------------
  const initialSeed = randomSeedString();
  document.getElementById('civSeedInput').value = initialSeed;
  generateWorld(initialSeed);
  resizeEntityCanvas();
  resizeGraph();
  bindUI();
  bindPointer();
  sampleHistory();
  renderTerrain();
  renderEntities();
  renderGraph();
})();

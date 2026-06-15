'use strict';

// ============================================================
// Constants
// ============================================================

const FILES = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'];
const ALPHABET = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';

// Both colors use the same (solid) glyph set; the outline glyphs
// (U+2654-2659) render as hollow shapes in most fonts and don't take a
// solid fill color, so white pieces would look like faint outlines.
// Using the filled glyphs for both and coloring via CSS keeps white
// pieces clearly visible as solid white pieces with a dark outline.
const PIECE_UNICODE = {
  w: { p: '♟', n: '♞', b: '♝', r: '♜', q: '♛', k: '♚' },
  b: { p: '♟', n: '♞', b: '♝', r: '♜', q: '♛', k: '♚' },
};

const PIECE_VALUES = { p: 100, n: 320, b: 330, r: 500, q: 900, k: 20000 };

const LEVEL_NAMES = {
  1: 'Random',
  2: 'Casual',
  3: 'Club player',
  4: 'Strong',
  5: 'Very strong',
};

const LEVEL_DEPTH = { 2: 1, 3: 2, 4: 3, 5: 4 };
const LEVEL_NOISE = { 2: 120, 3: 50, 4: 20, 5: 5 };

// ============================================================
// Global state
// ============================================================

const state = {
  game: null,
  playerColor: 'w',
  botLevel: 3,
  avgN: 3,
  challengeProb: 0.2,
  speakLetters: true,

  history: [],          // [{ply, color, san, from, to, letter, fen}]
  selectedSquare: null,
  legalTargets: [],
  pendingPromotion: null,

  challenge: null,       // {n, targetEntry, chosenLetter, letterCorrect}
  reconBoard: null,      // 8x8 array of {type,color} | null
  reconActivePiece: { type: 'p', color: 'w' },

  stats: { letterCorrect: 0, letterTotal: 0, posScoreSum: 0, posTotal: 0 },
  gameOver: false,
};

// ============================================================
// Helpers
// ============================================================

function otherColor(c) {
  return c === 'w' ? 'b' : 'w';
}

function randomLetter() {
  return ALPHABET[Math.floor(Math.random() * ALPHABET.length)];
}

function emptyBoard() {
  return Array.from({ length: 8 }, () => Array(8).fill(null));
}

function piecesEqual(a, b) {
  if (!a && !b) return true;
  if (!a || !b) return false;
  return a.type === b.type && a.color === b.color;
}

// Returns the [row,col] render order (chess.js board() indexing:
// row 0 = rank 8, row 7 = rank 1; col 0 = file a, col 7 = file h),
// flipped when the player is Black so their pieces sit at the bottom.
function boardOrder() {
  const order = [];
  for (let i = 0; i < 8; i++) {
    for (let j = 0; j < 8; j++) {
      if (state.playerColor === 'b') {
        order.push([7 - i, 7 - j]);
      } else {
        order.push([i, j]);
      }
    }
  }
  return order;
}

function squareName(r, c) {
  return FILES[c] + (8 - r);
}

// Letters are queued and spoken one at a time via our own queue rather
// than relying on the browser's internal speechSynthesis queue, which
// in Chrome can silently drop an utterance queued while another is in
// flight, or occasionally overlap two. We only start the next utterance
// once the previous one's onend/onerror fires (or a timeout elapses, in
// case Chrome gets permanently "stuck" and never fires either).
const speechQueue = [];
let speechBusy = false;

function speakLetter(letter) {
  if (!state.speakLetters) return;
  if (!('speechSynthesis' in window)) return;
  speechQueue.push(letter);
  pumpSpeechQueue();
}

function pumpSpeechQueue() {
  if (speechBusy) return;
  const letter = speechQueue.shift();
  if (letter === undefined) return;
  speechBusy = true;

  const utter = new SpeechSynthesisUtterance(letter);
  utter.rate = 0.85;

  const advance = () => {
    if (!speechBusy) return;
    speechBusy = false;
    pumpSpeechQueue();
  };
  utter.onend = advance;
  utter.onerror = advance;
  setTimeout(advance, 3000);

  speechSynthesis.resume();
  speechSynthesis.speak(utter);
}

// ============================================================
// Bot engine (negamax with alpha-beta pruning)
// ============================================================

function centerBonus(r, c, type) {
  if (type === 'k') return 0;
  const dist = Math.abs(3.5 - r) + Math.abs(3.5 - c);
  return Math.max(0, 4 - dist) * 2;
}

function evaluate(persp) {
  let score = 0;
  const board = state.game.board();
  for (let r = 0; r < 8; r++) {
    for (let c = 0; c < 8; c++) {
      const piece = board[r][c];
      if (!piece) continue;
      const val = PIECE_VALUES[piece.type] + centerBonus(r, c, piece.type);
      score += piece.color === persp ? val : -val;
    }
  }
  return score;
}

function negamax(depth, alpha, beta, persp) {
  const moves = state.game.moves({ verbose: true });
  if (moves.length === 0) {
    return state.game.in_check() ? -100000 : 0;
  }
  if (depth === 0) return evaluate(persp);

  moves.sort((a, b) => (b.captured ? 1 : 0) - (a.captured ? 1 : 0));

  let best = -Infinity;
  for (const m of moves) {
    state.game.move(m);
    const score = -negamax(depth - 1, -beta, -alpha, otherColor(persp));
    state.game.undo();
    if (score > best) best = score;
    if (best > alpha) alpha = best;
    if (alpha >= beta) break;
  }
  return best;
}

function chooseBotMove(level) {
  const moves = state.game.moves({ verbose: true });
  if (moves.length === 0) return null;
  if (level === 1) {
    return moves[Math.floor(Math.random() * moves.length)];
  }

  const depth = LEVEL_DEPTH[level] || 2;
  const noise = LEVEL_NOISE[level] || 0;
  const color = state.game.turn();

  const sorted = moves.slice().sort((a, b) => (b.captured ? 1 : 0) - (a.captured ? 1 : 0));

  let best = null;
  let bestScore = -Infinity;
  let alpha = -Infinity;
  const beta = Infinity;

  for (const m of sorted) {
    state.game.move(m);
    let score = -negamax(depth - 1, -beta, -alpha, otherColor(color));
    state.game.undo();
    score += (Math.random() * 2 - 1) * noise;
    if (score > bestScore) {
      bestScore = score;
      best = m;
    }
    if (score > alpha) alpha = score;
  }
  return best;
}

function botMove() {
  if (state.gameOver || state.challenge) return;
  const chosen = chooseBotMove(state.botLevel);
  if (!chosen) return;
  const move = state.game.move(chosen);
  afterPly(move);
}

// ============================================================
// Main board rendering & interaction
// ============================================================

function renderBoard() {
  const boardEl = document.getElementById('board');
  boardEl.innerHTML = '';

  const board = state.game.board();
  const last = state.history.length ? state.history[state.history.length - 1] : null;
  const inCheck = state.game.in_check();
  const turn = state.game.turn();

  for (const [r, c] of boardOrder()) {
    const name = squareName(r, c);
    const sq = document.createElement('div');
    const isLight = (r + c) % 2 === 0;
    sq.className = 'square ' + (isLight ? 'light' : 'dark');
    sq.dataset.square = name;

    const piece = board[r][c];
    if (piece) {
      sq.textContent = PIECE_UNICODE[piece.color][piece.type];
      sq.classList.add(piece.color === 'w' ? 'piece-white' : 'piece-black');
    }

    if (state.selectedSquare === name) sq.classList.add('selected');
    if (last && (last.from === name || last.to === name)) sq.classList.add('last-move');
    if (piece && piece.type === 'k' && piece.color === turn && inCheck) {
      sq.classList.add('in-check');
    }

    const target = state.legalTargets.find((t) => t.to === name);
    if (target) {
      const marker = document.createElement('div');
      marker.className = target.captured ? 'capture-ring' : 'move-dot';
      sq.appendChild(marker);
    }

    sq.addEventListener('click', () => handleSquareClick(name));
    boardEl.appendChild(sq);
  }
}

function handleSquareClick(name) {
  if (state.gameOver || state.challenge || state.pendingPromotion) return;
  if (state.game.turn() !== state.playerColor) return;

  const piece = state.game.get(name);

  if (state.selectedSquare) {
    if (name === state.selectedSquare) {
      clearSelection();
      return;
    }
    const target = state.legalTargets.find((t) => t.to === name);
    if (target) {
      attemptMove(state.selectedSquare, name);
      return;
    }
    if (piece && piece.color === state.playerColor) {
      selectSquare(name);
      return;
    }
    clearSelection();
    return;
  }

  if (piece && piece.color === state.playerColor) {
    selectSquare(name);
  }
}

function selectSquare(name) {
  state.selectedSquare = name;
  state.legalTargets = state.game.moves({ square: name, verbose: true });
  renderBoard();
}

function clearSelection() {
  state.selectedSquare = null;
  state.legalTargets = [];
  renderBoard();
}

function attemptMove(from, to) {
  const piece = state.game.get(from);
  const needsPromotion =
    piece.type === 'p' && ((piece.color === 'w' && to[1] === '8') || (piece.color === 'b' && to[1] === '1'));

  if (needsPromotion) {
    showPromotionPicker(from, to);
    return;
  }
  finalizeMove(from, to);
}

function finalizeMove(from, to, promotion) {
  const moveOpts = { from, to };
  if (promotion) moveOpts.promotion = promotion;
  const move = state.game.move(moveOpts);
  if (!move) return;
  state.selectedSquare = null;
  state.legalTargets = [];
  afterPly(move);
}

function showPromotionPicker(from, to) {
  state.pendingPromotion = { from, to };
  const picker = document.getElementById('promo-picker');
  picker.innerHTML = '';
  picker.classList.remove('hidden');

  for (const type of ['q', 'r', 'b', 'n']) {
    const btn = document.createElement('button');
    btn.textContent = PIECE_UNICODE[state.playerColor][type];
    btn.addEventListener('click', () => {
      picker.classList.add('hidden');
      const pending = state.pendingPromotion;
      state.pendingPromotion = null;
      finalizeMove(pending.from, pending.to, type);
    });
    picker.appendChild(btn);
  }
}

// ============================================================
// Game flow
// ============================================================

function afterPly(move) {
  const letter = randomLetter();
  state.history.push({
    ply: state.history.length + 1,
    color: move.color,
    san: move.san,
    from: move.from,
    to: move.to,
    letter,
    fen: state.game.fen(),
  });

  speakLetter(letter);
  renderBoard();
  updateStatus();

  if (checkGameOver()) return;

  const triggered = maybeTriggerChallenge();
  if (!triggered) {
    proceedTurn();
  }
}

function proceedTurn() {
  if (state.gameOver || state.challenge) return;
  if (state.game.turn() !== state.playerColor) {
    setThinking(true);
    setTimeout(botMove, 350);
  }
}

function setThinking(on) {
  if (!on) {
    updateStatus();
    return;
  }
  const botSide = state.playerColor === 'w' ? 'Black' : 'White';
  document.getElementById('turn-indicator').textContent = `${botSide} (bot) is thinking…`;
}

function updateStatus() {
  if (state.gameOver) return;
  const turnEl = document.getElementById('turn-indicator');
  const turn = state.game.turn() === 'w' ? 'White' : 'Black';
  let txt = `${turn} to move`;
  if (state.game.in_check()) txt += ' — Check!';
  turnEl.textContent = txt;
}

function checkGameOver() {
  if (!state.game.game_over()) return false;

  state.gameOver = true;
  let msg;
  if (state.game.in_checkmate()) {
    const winner = state.game.turn() === 'w' ? 'Black' : 'White';
    msg = `Checkmate — ${winner} wins!`;
  } else if (state.game.in_stalemate()) {
    msg = 'Draw — stalemate';
  } else if (state.game.insufficient_material()) {
    msg = 'Draw — insufficient material';
  } else if (state.game.in_threefold_repetition()) {
    msg = 'Draw — threefold repetition';
  } else if (state.game.in_draw()) {
    msg = 'Draw — 50-move rule';
  } else {
    msg = 'Game over';
  }
  document.getElementById('result-indicator').textContent = msg;
  document.getElementById('turn-indicator').textContent = 'Game over';
  return true;
}

// ============================================================
// N-back challenge
// ============================================================

// Roughly-Gaussian noise in (-2.5, 2.5), centered on 0, so the sampled n
// is usually avgN, sometimes avgN +/- 1, and occasionally avgN +/- 2.
function sampleNoise() {
  return (Math.random() + Math.random() + Math.random() + Math.random() - 2) * 1.25;
}

function maybeTriggerChallenge() {
  const total = state.history.length;
  if (total < 2) return false;
  if (Math.random() > state.challengeProb) return false;

  const maxN = total - 1;
  let n = Math.round(state.avgN + sampleNoise());
  n = Math.max(1, Math.min(n, maxN));

  const targetIndex = total - n; // 1-based ply number, always in [1, total-1]
  const targetEntry = state.history[targetIndex - 1];

  // Only squares that differ between the current position and the target
  // position need to be reconstructed; everything else is pre-filled.
  const currentBoard = state.game.board();
  const targetBoard = new Chess(targetEntry.fen).board();
  const diffSquares = [];
  state.reconBoard = emptyBoard();
  for (const [r, c] of boardOrder()) {
    if (piecesEqual(currentBoard[r][c], targetBoard[r][c])) {
      state.reconBoard[r][c] = currentBoard[r][c];
    } else {
      diffSquares.push([r, c]);
    }
  }

  state.challenge = {
    n,
    targetEntry,
    diffSquares,
    chosenLetter: null,
    letterCorrect: null,
  };

  state.reconActivePiece = { type: 'p', color: 'w' };

  showChallengeOverlay();
  return true;
}

function showChallengeOverlay() {
  const { n, diffSquares } = state.challenge;
  const moveWord = n === 1 ? 'move' : 'moves';

  document.getElementById('letter-prompt').textContent =
    `Memory check! Which letter was assigned ${n} ${moveWord} ago?`;

  if (diffSquares.length === 0) {
    document.getElementById('position-prompt').textContent =
      `Good news: the position hasn't changed in the last ${n} ${moveWord}. Nothing to rebuild!`;
  } else {
    const squareWord = diffSquares.length === 1 ? 'square' : 'squares';
    document.getElementById('position-prompt').textContent =
      `Now fill in the ${diffSquares.length} highlighted ${squareWord} as they were ${n} ${moveWord} ago.`;
  }

  renderLetterGrid();
  document.getElementById('challenge-overlay').classList.remove('hidden');
}

function renderLetterGrid() {
  const grid = document.getElementById('letter-grid');
  grid.innerHTML = '';
  for (const letter of ALPHABET) {
    const btn = document.createElement('button');
    btn.textContent = letter;
    btn.addEventListener('click', () => chooseLetterAnswer(letter, btn));
    grid.appendChild(btn);
  }
}

function chooseLetterAnswer(letter, btnEl) {
  if (state.challenge.chosenLetter) return;
  state.challenge.chosenLetter = letter;
  state.challenge.letterCorrect = letter === state.challenge.targetEntry.letter;

  document.querySelectorAll('#letter-grid button').forEach((b) => (b.disabled = true));
  btnEl.classList.add('chosen');

  if (state.challenge.diffSquares.length === 0) {
    document.getElementById('palette').classList.add('hidden');
  } else {
    renderPalette();
  }
  renderReconBoard();
  document.getElementById('challenge-step-position').classList.remove('hidden');
}

function renderPalette() {
  const palette = document.getElementById('palette');
  palette.innerHTML = '';

  const pieces = [
    { type: 'k', color: 'w' }, { type: 'q', color: 'w' }, { type: 'r', color: 'w' },
    { type: 'b', color: 'w' }, { type: 'n', color: 'w' }, { type: 'p', color: 'w' },
    { type: 'k', color: 'b' }, { type: 'q', color: 'b' }, { type: 'r', color: 'b' },
    { type: 'b', color: 'b' }, { type: 'n', color: 'b' }, { type: 'p', color: 'b' },
  ];

  for (const p of pieces) {
    const btn = document.createElement('button');
    btn.textContent = PIECE_UNICODE[p.color][p.type];
    btn.className = 'pal-piece ' + (p.color === 'w' ? 'piece-white' : 'piece-black');
    if (state.reconActivePiece && p.type === state.reconActivePiece.type && p.color === state.reconActivePiece.color) {
      btn.classList.add('active');
    }
    btn.addEventListener('click', () => setActivePiece(p, btn));
    palette.appendChild(btn);
  }

  const eraser = document.createElement('button');
  eraser.textContent = '✕';
  eraser.className = 'eraser';
  if (!state.reconActivePiece) eraser.classList.add('active');
  eraser.addEventListener('click', () => setActivePiece(null, eraser));
  palette.appendChild(eraser);
}

function setActivePiece(piece, btnEl) {
  state.reconActivePiece = piece;
  document.querySelectorAll('#palette button').forEach((b) => b.classList.remove('active'));
  btnEl.classList.add('active');
}

function renderReconBoard() {
  const boardEl = document.getElementById('recon-board');
  boardEl.innerHTML = '';

  const diffSet = new Set(state.challenge.diffSquares.map(([r, c]) => r + ',' + c));

  for (const [r, c] of boardOrder()) {
    const sq = document.createElement('div');
    const isLight = (r + c) % 2 === 0;
    sq.className = 'square ' + (isLight ? 'light' : 'dark');

    const isTarget = diffSet.has(r + ',' + c);
    sq.classList.add(isTarget ? 'recon-target' : 'recon-given');

    const piece = state.reconBoard[r][c];
    if (piece) {
      sq.textContent = PIECE_UNICODE[piece.color][piece.type];
      sq.classList.add(piece.color === 'w' ? 'piece-white' : 'piece-black');
    }

    if (isTarget) {
      sq.addEventListener('click', () => {
        state.reconBoard[r][c] = state.reconActivePiece ? { ...state.reconActivePiece } : null;
        renderReconBoard();
      });
    }

    boardEl.appendChild(sq);
  }
}

function submitPosition() {
  const target = state.challenge.targetEntry;
  const targetBoard = new Chess(target.fen).board();
  const diffSquares = state.challenge.diffSquares;

  let correct = 0;
  for (const [r, c] of diffSquares) {
    if (piecesEqual(state.reconBoard[r][c], targetBoard[r][c])) correct++;
  }
  const total = diffSquares.length;
  const posScore = total === 0 ? 1 : correct / total;

  state.stats.letterTotal++;
  if (state.challenge.letterCorrect) state.stats.letterCorrect++;
  state.stats.posTotal++;
  state.stats.posScoreSum += posScore;
  updateStatsDisplay();

  showChallengeResult(posScore, correct, total, targetBoard);
}

function showChallengeResult(posScore, correct, total, targetBoard) {
  document.getElementById('palette').classList.add('hidden');
  document.getElementById('submit-position').classList.add('hidden');
  document.getElementById('position-prompt').classList.add('hidden');

  renderDiffBoard(targetBoard);

  const pct = Math.round(posScore * 100);
  const letterOk = state.challenge.letterCorrect;
  const { n, chosenLetter, targetEntry } = state.challenge;
  const moveWord = n === 1 ? 'move' : 'moves';

  const positionLine = total === 0
    ? 'Position: nothing had changed — automatic full marks!'
    : `Position: ${correct}/${total} squares correct (${pct}%)`;

  const content = document.getElementById('result-content');
  content.innerHTML = `
    <div class="${letterOk ? 'good' : 'bad'}">
      Letter ${n} ${moveWord} ago: you said <strong>${chosenLetter}</strong>,
      correct was <strong>${targetEntry.letter}</strong> — ${letterOk ? 'Correct!' : 'Incorrect'}
    </div>
    <div class="big ${pct >= 80 ? 'good' : pct >= 50 ? '' : 'bad'}">
      ${positionLine}
    </div>
  `;

  document.getElementById('challenge-result').classList.remove('hidden');
}

function renderDiffBoard(targetBoard) {
  const boardEl = document.getElementById('recon-board');
  boardEl.innerHTML = '';

  const diffSet = new Set(state.challenge.diffSquares.map(([r, c]) => r + ',' + c));

  for (const [r, c] of boardOrder()) {
    const sq = document.createElement('div');
    const isLight = (r + c) % 2 === 0;
    sq.className = 'square ' + (isLight ? 'light' : 'dark');

    const piece = targetBoard[r][c];
    if (piece) {
      sq.textContent = PIECE_UNICODE[piece.color][piece.type];
      sq.classList.add(piece.color === 'w' ? 'piece-white' : 'piece-black');
    }

    if (diffSet.has(r + ',' + c)) {
      const userPiece = state.reconBoard[r][c];
      sq.classList.add(piecesEqual(userPiece, piece) ? 'diff-correct' : 'diff-wrong');
    } else {
      sq.classList.add('recon-given');
    }

    boardEl.appendChild(sq);
  }
}

function hideChallengeOverlay() {
  const overlay = document.getElementById('challenge-overlay');
  overlay.classList.add('hidden');

  // reset for next time
  document.getElementById('challenge-step-position').classList.add('hidden');
  document.getElementById('challenge-result').classList.add('hidden');
  document.getElementById('palette').classList.remove('hidden');
  document.getElementById('submit-position').classList.remove('hidden');
  document.getElementById('position-prompt').classList.remove('hidden');
}

function updateStatsDisplay() {
  const el = document.getElementById('stats-content');
  if (state.stats.posTotal === 0) {
    el.textContent = 'No challenges yet.';
    return;
  }
  const letterPct = Math.round((100 * state.stats.letterCorrect) / state.stats.letterTotal);
  const posPct = Math.round((100 * state.stats.posScoreSum) / state.stats.posTotal);
  el.innerHTML = `
    <div class="stat-row"><span>Challenges</span><span>${state.stats.posTotal}</span></div>
    <div class="stat-row"><span>Letter recall</span><span>${state.stats.letterCorrect}/${state.stats.letterTotal} (${letterPct}%)</span></div>
    <div class="stat-row"><span>Position accuracy</span><span>${posPct}%</span></div>
  `;
}

// ============================================================
// Setup screen / game start
// ============================================================

function updateSettingsSummary() {
  const el = document.getElementById('settings-summary');
  el.innerHTML = `
    <div>Bot strength: ${LEVEL_NAMES[state.botLevel]} (level ${state.botLevel})</div>
    <div>Playing as: ${state.playerColor === 'w' ? 'White' : 'Black'}</div>
    <div>Average N: ${state.avgN}</div>
    <div>Challenge frequency: ${Math.round(state.challengeProb * 100)}% per move</div>
  `;
}

function startGame() {
  state.playerColor = document.getElementById('player-color').value;
  state.botLevel = parseInt(document.getElementById('bot-level').value, 10);
  state.avgN = parseInt(document.getElementById('avg-n').value, 10);
  state.challengeProb = parseInt(document.getElementById('challenge-prob').value, 10) / 100;
  state.speakLetters = document.getElementById('speak-letters').checked;

  state.game = new Chess();
  state.history = [];
  state.selectedSquare = null;
  state.legalTargets = [];
  state.pendingPromotion = null;
  state.challenge = null;
  state.gameOver = false;
  state.stats = { letterCorrect: 0, letterTotal: 0, posScoreSum: 0, posTotal: 0 };

  document.getElementById('promo-picker').classList.add('hidden');
  document.getElementById('result-indicator').textContent = '';

  document.getElementById('setup-screen').classList.add('hidden');
  document.getElementById('game-screen').classList.remove('hidden');

  updateSettingsSummary();
  updateStatsDisplay();
  renderBoard();
  updateStatus();
  proceedTurn();
}

function backToSetup() {
  speechSynthesis.cancel();
  document.getElementById('game-screen').classList.add('hidden');
  document.getElementById('setup-screen').classList.remove('hidden');
}

// ============================================================
// Init
// ============================================================

document.addEventListener('DOMContentLoaded', () => {
  const avgN = document.getElementById('avg-n');
  const avgNVal = document.getElementById('avg-n-val');
  avgN.addEventListener('input', () => (avgNVal.textContent = avgN.value));

  const prob = document.getElementById('challenge-prob');
  const probVal = document.getElementById('challenge-prob-val');
  prob.addEventListener('input', () => (probVal.textContent = prob.value));

  document.getElementById('start-btn').addEventListener('click', startGame);
  document.getElementById('new-game-btn').addEventListener('click', backToSetup);
  document.getElementById('submit-position').addEventListener('click', submitPosition);
  document.getElementById('continue-btn').addEventListener('click', () => {
    hideChallengeOverlay();
    state.challenge = null;
    proceedTurn();
  });
});

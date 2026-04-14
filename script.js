/**
 * ═══════════════════════════════════════════════════════════
 *  CFG Derivation & Parse Tree Visualizer — script.js
 *  Author: Claude (Anthropic)
 *  Features:
 *    - Grammar parser & validator
 *    - Leftmost / Rightmost derivation (BFS)
 *    - Parse tree construction & SVG rendering
 *    - Zoom / pan / export PNG
 *    - Dark / light theme toggle
 *    - Animated step reveal
 * ═══════════════════════════════════════════════════════════
 */

'use strict';

/* ──────────────────────────────────────────
   STATE
────────────────────────────────────────── */
const state = {
  grammar:        null,   // { rules: Map<string, string[][]>, nonterminals: Set, terminals: Set }
  derivationSteps: [],
  parseTree:      null,
  zoom:           1.0,
  activeTab:      'derivation',
  animTimers:     [],
};

/* ──────────────────────────────────────────
   DOM REFS
────────────────────────────────────────── */
const $  = id => document.getElementById(id);
const $$ = sel => document.querySelectorAll(sel);

const grammarInput    = $('grammar-input');
const stringInput     = $('string-input');
const startSymbol     = $('start-symbol');
const stepsContainer  = $('steps-container');
const treeContainer   = $('tree-container');
const statusBar       = $('status-bar');
const parsedRulesList = $('parsed-rules-list');
const ruleCount       = $('rule-count');
const derivHeader     = $('deriv-header');
const derivTypeBadge  = $('deriv-type-badge');
const derivInfo       = $('deriv-info');
const treeToolbar     = $('tree-toolbar');
const zoomLabel       = $('zoom-label');
const rulesTrace      = $('rules-trace');
const treeRulesTrace  = $('tree-rules-trace');
const derivExplainer  = $('deriv-explainer');
const treeExplainer   = $('tree-explainer');

/* ──────────────────────────────────────────
   GRAMMAR PARSER
────────────────────────────────────────── */

/**
 * Parse raw grammar text into a structured format.
 * Supports:  A -> B C | d    and   A → B C | d
 * @param {string} text
 * @returns {{ rules: Map, nonterminals: Set, terminals: Set } | null}
 */
function parseGrammar(text) {
  const lines = text.split('\n')
    .map(l => l.trim())
    .filter(l => l && !l.startsWith('//') && !l.startsWith('#'));

  if (!lines.length) return null;

  // Pass 1: collect all nonterminals from LHS first.
  const nonterminals = new Set();
  for (const line of lines) {
    const normalized = line.replace(/→/g, '->').replace(/⟶/g, '->');
    const arrowIdx = normalized.indexOf('->');
    if (arrowIdx === -1) continue;
    const lhs = normalized.slice(0, arrowIdx).trim();
    if (lhs) nonterminals.add(lhs);
  }

  if (nonterminals.size === 0) return null;

  // Map: LHS -> array of productions, each production is array of symbols.
  const rules = new Map();

  function tokenizeProduction(alt) {
    if (alt === 'ε' || alt === 'eps' || alt === '') return [];

    // Explicit spacing always wins.
    if (/\s/.test(alt)) {
      return alt.split(/\s+/).filter(Boolean);
    }

    // No spaces: greedily match known nonterminals (longest first),
    // then treat lowercase/digit runs as one terminal token.
    const symbols = [];
    const ntsByLen = Array.from(nonterminals).sort((a, b) => b.length - a.length);
    let i = 0;

    while (i < alt.length) {
      let matched = null;
      for (const nt of ntsByLen) {
        if (nt && alt.startsWith(nt, i)) {
          matched = nt;
          break;
        }
      }

      if (matched) {
        symbols.push(matched);
        i += matched.length;
        continue;
      }

      const ch = alt[i];

      // Group lowercase/digit runs (e.g. id, num1).
      if (/[a-z0-9_]/.test(ch)) {
        let j = i + 1;
        while (j < alt.length && /[a-z0-9_]/.test(alt[j])) j++;
        symbols.push(alt.slice(i, j));
        i = j;
      } else {
        // Keep punctuation/operators as single tokens.
        symbols.push(ch);
        i++;
      }
    }

    return symbols;
  }

  for (const line of lines) {
    // Normalize arrow
    const normalized = line.replace(/→/g, '->').replace(/⟶/g, '->');
    const arrowIdx = normalized.indexOf('->');
    if (arrowIdx === -1) continue;

    const lhs = normalized.slice(0, arrowIdx).trim();
    const rhsRaw = normalized.slice(arrowIdx + 2).trim();

    if (!lhs) continue;

    // Split by | for alternatives
    const alternatives = rhsRaw.split('|').map(alt => alt.trim()).filter(a => a);
    const productions = alternatives.map(tokenizeProduction);

    if (!rules.has(lhs)) rules.set(lhs, []);
    rules.get(lhs).push(...productions);
  }

  if (rules.size === 0) return null;

  // Identify terminals
  const terminals    = new Set();

  for (const prods of rules.values()) {
    for (const prod of prods) {
      for (const sym of prod) {
        if (!nonterminals.has(sym)) terminals.add(sym);
      }
    }
  }

  return { rules, nonterminals, terminals };
}

/**
 * Validate grammar and return error message or null
 */
function validateGrammar(grammar, start) {
  if (!grammar) return 'No valid grammar rules found. Check your syntax (use A -> B C | d).';
  if (!grammar.rules.has(start)) return `Start symbol "${start}" not found in grammar rules.`;
  return null;
}

/* ──────────────────────────────────────────
   DERIVATION ENGINE  (BFS / CYK-like)
────────────────────────────────────────── */

/**
 * Parse tree node
 */
class ParseNode {
  constructor(symbol, children = []) {
    this.symbol   = symbol;
    this.children = children;   // ParseNode[]
    this.isTerminal = false;
  }
}

/**
 * Find leftmost or rightmost derivation using BFS.
 * Returns array of steps: { sentential: string[], appliedRule: {lhs, rhs, pos} | null }
 *
 * @param {Map}    rules
 * @param {Set}    nonterminals
 * @param {string} start
 * @param {string[]} target       - target terminal string
 * @param {'leftmost'|'rightmost'} mode
 * @param {number} maxDepth
 * @returns {{ steps: Array, tree: ParseNode } | null}
 */
function findDerivation(rules, nonterminals, start, target, mode, maxDepth = 30) {
  const targetStr = target.join('\x00');
  const targetLen = target.length;

  // Each state: sentential form, derivation steps so far, parse tree root
  const initial = {
    sentential: [start],
    steps: [{ sentential: [start], rule: null }],
    treeNode: new ParseNode(start),
  };

  const queue   = [initial];
  // FIX: key is ONLY the sentential string — do NOT include expandIdx.
  // Using expandIdx in the key caused valid paths to be pruned when the
  // same sentential form was reached via a different expansion position.
  const visited = new Set([start]);

  while (queue.length > 0) {
    const { sentential, steps, treeNode } = queue.shift();

    if (steps.length > maxDepth + 1) continue;

    // Check if fully terminal
    const isAllTerminal = sentential.every(s => !nonterminals.has(s));

    if (isAllTerminal) {
      const sentStr = sentential.length === 0 ? '' : sentential.join('\x00');
      if (sentStr === targetStr) {
        return { steps, tree: treeNode };
      }
      continue;
    }

    // Find which NT to expand
    let expandIdx = -1;
    if (mode === 'leftmost') {
      expandIdx = sentential.findIndex(s => nonterminals.has(s));
    } else {
      for (let i = sentential.length - 1; i >= 0; i--) {
        if (nonterminals.has(sentential[i])) { expandIdx = i; break; }
      }
    }
    if (expandIdx === -1) continue;

    const nt    = sentential[expandIdx];
    const prods = rules.get(nt) || [];

    for (const prod of prods) {
      const newSentential = [
        ...sentential.slice(0, expandIdx),
        ...prod,
        ...sentential.slice(expandIdx + 1),
      ];

      // Prune 1: sentential too long to ever match target
      if (newSentential.length > targetLen + 4) continue;

      // Prune 2: if fully terminal and doesn't match, skip
      if (newSentential.every(s => !nonterminals.has(s))) {
        if (newSentential.join('\x00') !== targetStr) continue;
      }

      // Prune 3: count terminals already fixed; if they don't prefix-match, skip
      const terminalPrefix = [];
      let allMatch = true;
      for (const sym of newSentential) {
        if (!nonterminals.has(sym)) terminalPrefix.push(sym);
        else break;
      }
      for (let i = 0; i < terminalPrefix.length; i++) {
        if (terminalPrefix[i] !== target[i]) { allMatch = false; break; }
      }
      if (!allMatch) continue;

      // FIX: key is only the sentential content, not position-dependent
      const key = newSentential.join('\x00');
      if (visited.has(key)) continue;
      visited.add(key);

      // Build parse tree: deep clone and expand the right node
      const newTree = cloneTree(treeNode);
      const nodeToExpand = findUnexpandedNode(newTree, nonterminals, mode);
      if (nodeToExpand) {
        nodeToExpand.children = prod.map(s => {
          const n = new ParseNode(s === '' ? 'ε' : s);
          n.isTerminal = !nonterminals.has(s);
          return n;
        });
        nodeToExpand._expanded = true;
      }

      queue.push({
        sentential: newSentential,
        steps: [...steps, {
          sentential: newSentential,
          rule: { lhs: nt, rhs: prod, pos: expandIdx },
        }],
        treeNode: newTree,
      });
    }
  }

  return null;
}

/** Deep-clone a parse tree */
function cloneTree(node) {
  const n = new ParseNode(node.symbol, node.children.map(cloneTree));
  n.isTerminal = node.isTerminal;
  n._expanded  = node._expanded;
  return n;
}

/** Find the first unexpanded NT node (leftmost DFS or rightmost) */
function findUnexpandedNode(node, nonterminals, mode) {
  const candidates = [];
  function dfs(n) {
    if (!n.isTerminal && !n._expanded && nonterminals.has(n.symbol)) {
      candidates.push(n);
    }
    for (const c of n.children) dfs(c);
  }
  dfs(node);
  if (!candidates.length) return null;
  return mode === 'rightmost' ? candidates[candidates.length - 1] : candidates[0];
}



/**
 * Render derivation steps with staggered animation
 */
function renderDerivationSteps(steps, mode, grammar) {
  const { nonterminals } = grammar;

  // Clear old timers
  state.animTimers.forEach(t => clearTimeout(t));
  state.animTimers = [];

  stepsContainer.innerHTML = '';
  derivHeader.style.display = 'flex';

  derivTypeBadge.textContent = mode === 'leftmost' ? 'Leftmost' : 'Rightmost';
  derivTypeBadge.style.background = mode === 'leftmost'
    ? 'linear-gradient(135deg, var(--accent), var(--accent3))'
    : 'linear-gradient(135deg, var(--accent2), var(--accent3))';

  derivInfo.textContent = `${steps.length - 1} derivation step${steps.length === 2 ? '' : 's'}`;
  renderAppliedRuleTrace(steps, rulesTrace, `${mode === 'leftmost' ? 'Leftmost' : 'Rightmost'} Rule Sequence`);

  steps.forEach((step, i) => {
    const isFirst = i === 0;
    const isFinal = i === steps.length - 1;
    const delay   = isFirst ? 0 : i * 180;

    const timer = setTimeout(() => {
      const row = document.createElement('div');
      row.className = 'step-row' + (isFinal ? ' step-final' : '');
      row.style.animationDelay = '0ms';

      // Step number
      const numEl = document.createElement('div');
      numEl.className = 'step-num';
      numEl.textContent = i.toString().padStart(2, '0');

      // Arrow (not on first)
      const arrowEl = document.createElement('div');
      arrowEl.className = 'step-arrow';
      arrowEl.textContent = isFirst ? '  ' : '⇒';

      // Content — color-code symbols
      const contentEl = document.createElement('div');
      contentEl.className = 'step-content';
      contentEl.innerHTML = formatSentential(step.sentential, nonterminals, step.rule);

      // Rule label
      const ruleEl = document.createElement('div');
      ruleEl.className = 'step-rule';
      if (step.rule && !isFinal) {
        const prod = step.rule.rhs.length === 0 ? 'ε' : step.rule.rhs.join(' ');
        ruleEl.innerHTML = `<span class="rule-pill">${step.rule.lhs} → ${escapeHtml(prod)}</span>`;
      } else if (isFinal) {
        ruleEl.innerHTML = `<span class="rule-pill" style="color:var(--success);border-color:var(--success)">✓ accepted</span>`;
      }

      row.appendChild(numEl);
      row.appendChild(arrowEl);
      row.appendChild(contentEl);
      row.appendChild(ruleEl);
      stepsContainer.appendChild(row);

      // Scroll to keep latest visible
      stepsContainer.scrollTop = stepsContainer.scrollHeight;
    }, delay);

    state.animTimers.push(timer);
  });
}

/**
 * Render the production rules used in order for a generated derivation.
 */
function renderAppliedRuleTrace(steps, container, title) {
  if (!container) return;

  const applied = steps
    .map((step, idx) => ({ idx, rule: step.rule }))
    .filter(item => item.rule);

  if (!applied.length) {
    container.style.display = 'none';
    container.innerHTML = '';
    return;
  }

  const itemsHtml = applied.map((item, seqIdx) => {
    const rhs = item.rule.rhs.length ? item.rule.rhs.join(' ') : 'ε';
    return `
      <div class="trace-item">
        <span class="trace-step">R${seqIdx + 1}</span>
        <span class="trace-prod">${escapeHtml(item.rule.lhs)} → ${escapeHtml(rhs)}</span>
      </div>`;
  }).join('');

  container.innerHTML = `
    <div class="trace-title">${escapeHtml(title)} (${applied.length})</div>
    <div class="trace-list">${itemsHtml}</div>
  `;
  container.style.display = 'block';
}

/**
 * Render explanatory text describing what happens in each generation step.
 */
function renderStepExplanations({ steps, mode, start, target, container, title }) {
  if (!container || !steps || !steps.length) return;

  const modeLabel = mode === 'rightmost' ? 'rightmost' : 'leftmost';
  const targetDisplay = target.length ? target.join(' ') : 'ε';

  const staticLines = [
    'Read grammar and parse production rules into structured alternatives.',
    `Tokenize input string as terminal sequence: ${escapeHtml(targetDisplay)}.`,
    `Start derivation from the start symbol ${escapeHtml(start)}.`,
    `At each step, expand exactly one nonterminal using ${modeLabel} strategy.`,
    'Stop when all symbols are terminals and match the target input.',
  ];

  const dynamicLines = [];
  for (let i = 1; i < steps.length; i++) {
    const prev = steps[i - 1];
    const curr = steps[i];
    if (!curr.rule) continue;

    const rhs = curr.rule.rhs.length ? curr.rule.rhs.join(' ') : 'ε';
    const before = prev.sentential.length ? prev.sentential.join(' ') : 'ε';
    const after = curr.sentential.length ? curr.sentential.join(' ') : 'ε';

    dynamicLines.push(
      `Step ${i}: expanded ${curr.rule.lhs} at position ${curr.rule.pos + 1} using ${curr.rule.lhs} -> ${rhs}; ${before} => ${after}`
    );
  }

  const staticHtml = staticLines
    .map(line => `<div class="explain-item">• ${escapeHtml(line)}</div>`)
    .join('');

  const dynamicHtml = dynamicLines.length
    ? dynamicLines.map(line => `<div class="dynamic-item">${escapeHtml(line)}</div>`).join('')
    : '<div class="dynamic-item">No rewrite step generated yet.</div>';

  container.innerHTML = `
    <div class="explain-title">${escapeHtml(title)}</div>
    <div class="explain-list">${staticHtml}</div>
    <div class="explain-dynamic">${dynamicHtml}</div>
  `;
  container.style.display = 'block';
}

function renderParseTreeExplanations({ steps, start, target, container }) {
  if (!container || !steps || !steps.length) return;

  const targetDisplay = target.length ? target.join(' ') : 'ε';
  const staticLines = [
    `Build root node from start symbol ${escapeHtml(start)}.`,
    'Follow a successful derivation (leftmost in this implementation).',
    'For each applied rule, add RHS symbols as children of the expanded nonterminal node.',
    'Mark terminal symbols as leaf nodes; nonterminals remain expandable until rewritten.',
    `When leaf sequence matches ${escapeHtml(targetDisplay)}, finalize parse tree.`
  ];

  const dynamicLines = [];
  for (let i = 1; i < steps.length; i++) {
    const curr = steps[i];
    if (!curr.rule) continue;
    const rhs = curr.rule.rhs.length ? curr.rule.rhs.join(' ') : 'ε';
    dynamicLines.push(
      `Tree step ${i}: node ${curr.rule.lhs} expanded with children [${rhs}]`
    );
  }

  container.innerHTML = `
    <div class="explain-title">Parse Tree Construction Steps</div>
    <div class="explain-list">
      ${staticLines.map(line => `<div class="explain-item">• ${line}</div>`).join('')}
    </div>
    <div class="explain-dynamic">
      ${dynamicLines.length ? dynamicLines.map(line => `<div class="dynamic-item">${escapeHtml(line)}</div>`).join('') : '<div class="dynamic-item">No tree step generated yet.</div>'}
    </div>
  `;
  container.style.display = 'block';
}

/**
 * Format sentential form as HTML with colored symbols
 */
function formatSentential(sentential, nonterminals, rule) {
  if (sentential.length === 0) return '<span class="term">ε</span>';
  return sentential.map((sym, idx) => {
    const isNT   = nonterminals.has(sym);
    const isExpanded = rule && idx === rule.pos;
    if (isNT) {
      return `<span class="nt${isExpanded ? ' expanded' : ''}">${escapeHtml(sym)}</span>`;
    }
    return `<span class="term">${escapeHtml(sym)}</span>`;
  }).join('<span class="arrow-sym"> </span>');
}

/* ──────────────────────────────────────────
   RENDERING — PARSE TREE  (SVG)
────────────────────────────────────────── */

/** Layout constants */
const TREE = {
  NODE_R:    22,   // circle radius
  H_GAP:     52,   // min horizontal gap between nodes
  V_GAP:     70,   // vertical gap between levels
  PADDING:   40,   // outer padding
};

/**
 * Compute positions for all nodes using post-order width calculation
 */
function layoutTree(root) {
  // Assign widths bottom-up
  function computeWidth(node) {
    if (node.children.length === 0) {
      node._width = TREE.NODE_R * 2 + TREE.H_GAP;
      return node._width;
    }
    node._width = node.children.reduce((sum, c) => sum + computeWidth(c), 0);
    node._width = Math.max(node._width, TREE.NODE_R * 2 + TREE.H_GAP);
    return node._width;
  }

  // Assign x/y coordinates top-down
  function assignPos(node, left, depth) {
    node._x = left + node._width / 2;
    node._y = TREE.PADDING + depth * TREE.V_GAP;

    let childLeft = left;
    for (const c of node.children) {
      assignPos(c, childLeft, depth + 1);
      childLeft += c._width;
    }
  }

  computeWidth(root);
  assignPos(root, TREE.PADDING, 0);

  // Find total dimensions
  let maxX = 0, maxY = 0;
  function measure(node) {
    maxX = Math.max(maxX, node._x + TREE.NODE_R + TREE.PADDING);
    maxY = Math.max(maxY, node._y + TREE.NODE_R + TREE.PADDING);
    for (const c of node.children) measure(c);
  }
  measure(root);

  return { width: maxX, height: maxY };
}

/**
 * Render parse tree to SVG
 */
function renderParseTree(root) {
  const { width, height } = layoutTree(root);

  const svgNS = 'http://www.w3.org/2000/svg';
  const svg   = document.createElementNS(svgNS, 'svg');
  svg.setAttribute('id', 'tree-svg');
  svg.setAttribute('width',  width);
  svg.setAttribute('height', height);
  svg.setAttribute('viewBox', `0 0 ${width} ${height}`);
  svg.setAttribute('xmlns', svgNS);

  // Resolve current theme colors for use throughout the SVG
  const _cs       = getComputedStyle(document.documentElement);
  const _accent   = _cs.getPropertyValue('--accent').trim();
  const _accent2  = _cs.getPropertyValue('--accent2').trim();
  const _surface2 = _cs.getPropertyValue('--surface2').trim();
  const _border   = _cs.getPropertyValue('--border').trim();

  // Defs — no gradient fill needed; just store accent refs for export use
  const defs = document.createElementNS(svgNS, 'defs');
  svg.appendChild(defs);

  // Expose resolved colors on svg element so exportPNG can read them
  svg._themeColors = { accent: _accent, accent2: _accent2, surface2: _surface2, border: _border };

  // Collect all edges and nodes for ordered rendering
  const edges = [];
  const nodes = [];
  let nodeIdx = 0;

  function collect(node) {
    for (const child of node.children) {
      edges.push({ x1: node._x, y1: node._y, x2: child._x, y2: child._y });
      collect(child);
    }
    nodes.push({ node, idx: nodeIdx++ });
  }
  collect(root);

  // Draw edges first (behind nodes)
  const edgeGroup = document.createElementNS(svgNS, 'g');
  edgeGroup.setAttribute('class', 'edges');
  edges.forEach((e, idx) => {
    const line = document.createElementNS(svgNS, 'line');
    line.setAttribute('x1', e.x1); line.setAttribute('y1', e.y1);
    line.setAttribute('x2', e.x2); line.setAttribute('y2', e.y2);
    line.setAttribute('class', 'tree-edge');
    line.style.strokeDasharray = Math.hypot(e.x2 - e.x1, e.y2 - e.y1);
    line.style.strokeDashoffset = Math.hypot(e.x2 - e.x1, e.y2 - e.y1);
    line.style.animation = `drawEdge 0.4s ease ${idx * 60}ms forwards`;
    edgeGroup.appendChild(line);
  });
  svg.appendChild(edgeGroup);

  // Draw nodes
  const nodeGroup = document.createElementNS(svgNS, 'g');
  nodeGroup.setAttribute('class', 'nodes');
  nodes.forEach(({ node, idx }) => {
    const g = document.createElementNS(svgNS, 'g');
    g.style.opacity = '0';
    g.style.animation = `nodePop 0.35s cubic-bezier(0.34,1.56,0.64,1) ${50 + idx * 45}ms forwards`;

    const circle = document.createElementNS(svgNS, 'circle');
    circle.setAttribute('cx', node._x);
    circle.setAttribute('cy', node._y);
    circle.setAttribute('r',  TREE.NODE_R);
    circle.setAttribute('fill', _surface2);
    circle.setAttribute('stroke', node.isTerminal ? _accent2 : _accent);
    circle.setAttribute('stroke-width', '1.5');
    circle.setAttribute('class', `tree-node-circle ${node.isTerminal ? 'tree-node-term' : 'tree-node-nt'}`);

    const text = document.createElementNS(svgNS, 'text');
    text.setAttribute('x', node._x);
    text.setAttribute('y', node._y);
    text.setAttribute('class', `tree-node-text ${node.isTerminal ? 'tree-node-text-term' : 'tree-node-text-nt'}`);
    text.textContent = node.symbol;

    // Scale down long symbols
    if (node.symbol.length > 3) {
      text.setAttribute('font-size', '10');
    } else if (node.symbol.length > 2) {
      text.setAttribute('font-size', '11');
    }

    // Tooltip
    const title = document.createElementNS(svgNS, 'title');
    title.textContent = node.isTerminal ? `Terminal: ${node.symbol}` : `Nonterminal: ${node.symbol}`;
    g.appendChild(title);

    g.appendChild(circle);
    g.appendChild(text);
    nodeGroup.appendChild(g);
  });
  svg.appendChild(nodeGroup);

  // Add keyframes for edge drawing
  if (!document.getElementById('tree-keyframes')) {
    const style = document.createElement('style');
    style.id = 'tree-keyframes';
    style.textContent = `
      @keyframes drawEdge {
        to { stroke-dashoffset: 0; }
      }
      @keyframes nodePop {
        0%   { opacity:0; transform: scale(0); }
        60%  { opacity:1; transform: scale(1.12); }
        100% { opacity:1; transform: scale(1); }
      }
    `;
    document.head.appendChild(style);
  }

  return svg;
}

/* ──────────────────────────────────────────
   GRAMMAR RULES DISPLAY
────────────────────────────────────────── */

function renderParsedRules(grammar) {
  if (!grammar) {
    parsedRulesList.innerHTML = '<p class="empty-hint">Enter grammar rules above to see them parsed here.</p>';
    ruleCount.textContent = '0 rules';
    return;
  }

  const { rules, nonterminals, terminals } = grammar;
  parsedRulesList.innerHTML = '';

  let totalProds = 0;
  let rowIndex   = 0;

  for (const [lhs, prods] of rules) {
    totalProds += prods.length;
    const row = document.createElement('div');
    row.className = 'rule-row';
    row.style.animationDelay = `${rowIndex * 60}ms`;

    const lhsEl = document.createElement('span');
    lhsEl.className = 'rule-lhs';
    lhsEl.textContent = lhs;

    const arrowEl = document.createElement('span');
    arrowEl.className = 'rule-arrow';
    arrowEl.textContent = '→';

    const rhsEl = document.createElement('span');
    rhsEl.className = 'rule-rhs';
    rhsEl.innerHTML = prods.map((prod, i) => {
      const prodHtml = prod.length === 0
        ? '<span class="terminal">ε</span>'
        : prod.map(s => {
            if (nonterminals.has(s)) return `<span class="nonterminal">${escapeHtml(s)}</span>`;
            return `<span class="terminal">${escapeHtml(s)}</span>`;
          }).join(' ');
      return (i > 0 ? '<span class="pipe">|</span>' : '') + prodHtml;
    }).join('');

    row.appendChild(lhsEl);
    row.appendChild(arrowEl);
    row.appendChild(rhsEl);
    parsedRulesList.appendChild(row);
    rowIndex++;
  }

  ruleCount.textContent = `${rules.size} rule${rules.size !== 1 ? 's' : ''} · ${totalProds} production${totalProds !== 1 ? 's' : ''}`;
}

/* ──────────────────────────────────────────
   STATUS BAR
────────────────────────────────────────── */

function setStatus(type, message) {
  const icons = {
    idle:    '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="10"/><line x1="12" y1="8" x2="12" y2="12"/><line x1="12" y1="16" x2="12.01" y2="16"/></svg>',
    success: '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polyline points="20 6 9 17 4 12"/></svg>',
    error:   '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="10"/><line x1="15" y1="9" x2="9" y2="15"/><line x1="9" y1="9" x2="15" y2="15"/></svg>',
    loading: '<div class="spinner"></div>',
  };
  statusBar.innerHTML = `<div class="status-${type}">${icons[type] || ''} ${message}</div>`;
}

/* ──────────────────────────────────────────
   TOAST
────────────────────────────────────────── */

function showToast(msg, duration = 2500) {
  const toast = $('toast');
  toast.textContent = msg;
  toast.classList.add('show');
  setTimeout(() => toast.classList.remove('show'), duration);
}

/* ──────────────────────────────────────────
   TABS
────────────────────────────────────────── */

function switchTab(name) {
  state.activeTab = name;
  $$('.tab-btn').forEach(btn => btn.classList.toggle('active', btn.dataset.tab === name));
  $$('.tab-content').forEach(el => el.classList.toggle('active', el.id === 'tab-' + name));
}

/* ──────────────────────────────────────────
   ZOOM
────────────────────────────────────────── */

function setZoom(z) {
  state.zoom = Math.min(2.0, Math.max(0.3, z));
  const svg = document.getElementById('tree-svg');
  if (svg) svg.style.transform = `scale(${state.zoom})`;
  zoomLabel.textContent = Math.round(state.zoom * 100) + '%';
}

/* ──────────────────────────────────────────
   EXPORT PNG
────────────────────────────────────────── */

function exportPNG() {
  const svg = document.getElementById('tree-svg');
  if (!svg) { showToast('No parse tree to export!'); return; }

  // Get theme colors — prefer stored values from renderParseTree, fall back to computed
  const cs      = getComputedStyle(document.documentElement);
  const tc      = svg._themeColors || {};
  const accent  = tc.accent   || cs.getPropertyValue('--accent').trim();
  const accent2 = tc.accent2  || cs.getPropertyValue('--accent2').trim();
  const surface2= tc.surface2 || cs.getPropertyValue('--surface2').trim();
  const border  = tc.border   || cs.getPropertyValue('--border').trim();
  const bg      = cs.getPropertyValue('--bg').trim();
  const text    = cs.getPropertyValue('--text').trim();

  // Clone so we never mutate the live tree
  const clone = svg.cloneNode(true);

  // ── Reset animation state to final (visible) values ──────────
  // Node groups start at opacity:0 via inline style — make them visible
  clone.querySelectorAll('.nodes g').forEach(g => {
    g.style.opacity    = '1';
    g.style.animation  = 'none';
    g.style.transform  = 'none';
  });
  // Edges use strokeDashoffset to hide until animated — reset to 0
  clone.querySelectorAll('.tree-edge').forEach(line => {
    line.style.strokeDashoffset = '0';
    line.style.animation        = 'none';
  });

  // ── Inject inlined style block so CSS classes resolve ────────
  const styleEl = document.createElementNS('http://www.w3.org/2000/svg', 'style');
  styleEl.textContent = `
    .tree-edge        { fill:none; stroke:${border}; stroke-width:1.5; }
    .tree-node-text   { font-family:monospace; font-size:13px; font-weight:600;
                        text-anchor:middle; dominant-baseline:central; }
    .tree-node-text-nt   { fill:${accent}; }
    .tree-node-text-term { fill:${accent2}; }
  `;
  clone.insertBefore(styleEl, clone.firstChild);

  // ── Draw to canvas ───────────────────────────────────────────
  const svgStr = new XMLSerializer().serializeToString(clone);
  const W = parseInt(svg.getAttribute('width'));
  const H = parseInt(svg.getAttribute('height'));
  const canvas = document.createElement('canvas');
  const scale  = 2;
  canvas.width  = W * scale;
  canvas.height = H * scale;
  const ctx = canvas.getContext('2d');
  ctx.fillStyle = bg || '#0f0e13';
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  ctx.scale(scale, scale);

  const img = new Image();
  img.onload = () => {
    ctx.drawImage(img, 0, 0);
    const link = document.createElement('a');
    link.download = 'parse-tree.png';
    link.href = canvas.toDataURL('image/png');
    link.click();
    showToast('Parse tree saved as PNG');
  };
  img.onerror = () => showToast('Export failed — try again');
  // encodeURIComponent is safer than btoa for Unicode SVG content
  img.src = 'data:image/svg+xml;charset=utf-8,' + encodeURIComponent(svgStr);
}

/* ──────────────────────────────────────────
   UTILITY
────────────────────────────────────────── */

function escapeHtml(str) {
  return String(str)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

function tokenizeInput(str, grammar) {
  str = str.trim();
  if (!str || str === 'ε') return [];

  // Explicit token spacing always wins.
  if (/\s/.test(str)) return str.split(/\s+/).filter(Boolean);

  // If grammar is available, greedily match known terminals first.
  if (grammar && grammar.terminals && grammar.terminals.size > 0) {
    const termsByLen = Array.from(grammar.terminals)
      .filter(t => t && t !== 'ε')
      .sort((a, b) => b.length - a.length);

    const out = [];
    let i = 0;
    while (i < str.length) {
      let matched = null;
      for (const t of termsByLen) {
        if (str.startsWith(t, i)) {
          matched = t;
          break;
        }
      }
      if (matched) {
        out.push(matched);
        i += matched.length;
      } else {
        // Fallback: keep progress by single char.
        out.push(str[i]);
        i++;
      }
    }
    return out;
  }

  // Last fallback: character-wise tokens.
  return str.split('');
}

/* ──────────────────────────────────────────
   MAIN ACTIONS
────────────────────────────────────────── */

/**
 * Get & validate grammar + input, return null on error
 */
function getInputs() {
  const grammarText = grammarInput.value;
  const inputStr    = stringInput.value;
  const start       = startSymbol.value.trim();

  const grammar = parseGrammar(grammarText);
  const err     = validateGrammar(grammar, start);
  if (err) {
    setStatus('error', err);
    showToast('⚠ ' + err);
    return null;
  }

  // Render parsed rules
  state.grammar = grammar;
  renderParsedRules(grammar);

  const target = tokenizeInput(inputStr, grammar);
  return { grammar, target, start };
}

/** Generate Leftmost Derivation */
function doLeftmostDerivation() {
  const inp = getInputs();
  if (!inp) return;
  const { grammar, target, start } = inp;

  setStatus('loading', 'Computing leftmost derivation…');
  switchTab('derivation');

  // Async to allow UI update
  setTimeout(() => {
    const result = findDerivation(grammar.rules, grammar.nonterminals, start, target, 'leftmost');
    if (!result) {
      setStatus('error', `"${target.join('')}" cannot be derived from ${start} (leftmost). Check grammar and string.`);
      stepsContainer.innerHTML = `<div class="empty-state"><div class="empty-icon">⚠️</div><p class="empty-title">No Derivation Found</p><p class="empty-sub">The string may not be in the language of this grammar.</p></div>`;
      rulesTrace.style.display = 'none';
      rulesTrace.innerHTML = '';
      derivExplainer.style.display = 'none';
      derivExplainer.innerHTML = '';
      return;
    }
    setStatus('success', `Leftmost derivation found — ${result.steps.length - 1} step${result.steps.length === 2 ? '' : 's'}`);
    state.derivationSteps = result.steps;
    state.parseTree       = result.tree;
    renderDerivationSteps(result.steps, 'leftmost', grammar);
    renderStepExplanations({
      steps: result.steps,
      mode: 'leftmost',
      start,
      target,
      container: derivExplainer,
      title: 'Leftmost Derivation: What Happens Internally',
    });
  }, 50);
}

/** Generate Rightmost Derivation */
function doRightmostDerivation() {
  const inp = getInputs();
  if (!inp) return;
  const { grammar, target, start } = inp;

  setStatus('loading', 'Computing rightmost derivation…');
  switchTab('derivation');

  setTimeout(() => {
    const result = findDerivation(grammar.rules, grammar.nonterminals, start, target, 'rightmost');
    if (!result) {
      setStatus('error', `"${target.join('')}" cannot be derived from ${start} (rightmost).`);
      stepsContainer.innerHTML = `<div class="empty-state"><p class="empty-title">No Derivation Found</p><p class="empty-sub">The string may not be in the language of this grammar.</p></div>`;
      rulesTrace.style.display = 'none';
      rulesTrace.innerHTML = '';
      derivExplainer.style.display = 'none';
      derivExplainer.innerHTML = '';
      return;
    }
    setStatus('success', `Rightmost derivation found — ${result.steps.length - 1} step${result.steps.length === 2 ? '' : 's'}`);
    state.derivationSteps = result.steps;
    state.parseTree       = result.tree;
    renderDerivationSteps(result.steps, 'rightmost', grammar);
    renderStepExplanations({
      steps: result.steps,
      mode: 'rightmost',
      start,
      target,
      container: derivExplainer,
      title: 'Rightmost Derivation: What Happens Internally',
    });
  }, 50);
}

/** Generate Parse Tree */
function doParseTree() {
  const inp = getInputs();
  if (!inp) return;
  const { grammar, target, start } = inp;

  setStatus('loading', 'Building parse tree…');
  switchTab('tree');

  setTimeout(() => {
    // Try leftmost first to get tree
    const result = findDerivation(grammar.rules, grammar.nonterminals, start, target, 'leftmost');
    if (!result) {
      setStatus('error', `Cannot build parse tree — "${target.join('')}" is not in L(G).`);
      treeContainer.innerHTML = `<div class="empty-state"><p class="empty-title">No Parse Tree</p><p class="empty-sub">The string cannot be derived from this grammar.</p></div>`;
      treeToolbar.style.display = 'none';
      treeRulesTrace.style.display = 'none';
      treeRulesTrace.innerHTML = '';
      treeExplainer.style.display = 'none';
      treeExplainer.innerHTML = '';
      return;
    }

    setStatus('success', `Parse tree generated for "${target.join(' ') || 'ε'}"`);
    state.parseTree = result.tree;
    treeToolbar.style.display = 'flex';
    renderAppliedRuleTrace(result.steps, treeRulesTrace, 'Rules Used For Parse Tree');
    renderParseTreeExplanations({ steps: result.steps, start, target, container: treeExplainer });
    treeContainer.innerHTML = '';
    state.zoom = 1.0;
    zoomLabel.textContent = '100%';

    const svg = renderParseTree(result.tree);
    treeContainer.appendChild(svg);
  }, 50);
}

/** Clear everything */
function clearAll() {
  grammarInput.value = '';
  stringInput.value  = '';
  startSymbol.value  = 'S';
  state.grammar      = null;
  state.derivationSteps = [];
  state.parseTree    = null;
  state.animTimers.forEach(t => clearTimeout(t));
  state.animTimers   = [];

  stepsContainer.innerHTML = `<div class="empty-state"><div class="empty-icon"><svg width="48" height="48" viewBox="0 0 48 48" fill="none"><circle cx="24" cy="14" r="6" stroke="var(--accent)" stroke-width="1.5" stroke-dasharray="3 2"/><circle cx="12" cy="36" r="6" stroke="var(--accent2)" stroke-width="1.5" stroke-dasharray="3 2"/><circle cx="36" cy="36" r="6" stroke="var(--accent3)" stroke-width="1.5" stroke-dasharray="3 2"/><line x1="24" y1="20" x2="12" y2="30" stroke="var(--border)" stroke-width="1.5"/><line x1="24" y1="20" x2="36" y2="30" stroke="var(--border)" stroke-width="1.5"/></svg></div><p class="empty-title">No Derivation Yet</p><p class="empty-sub">Configure your grammar and click one of the derivation buttons</p></div>`;

  treeContainer.innerHTML = `<div class="empty-state"><div class="empty-icon"><svg width="48" height="48" viewBox="0 0 48 48" fill="none"><rect x="16" y="4" width="16" height="12" rx="3" stroke="var(--accent)" stroke-width="1.5" stroke-dasharray="3 2"/><rect x="4" y="32" width="14" height="12" rx="3" stroke="var(--accent2)" stroke-width="1.5" stroke-dasharray="3 2"/><rect x="30" y="32" width="14" height="12" rx="3" stroke="var(--accent3)" stroke-width="1.5" stroke-dasharray="3 2"/><line x1="24" y1="16" x2="11" y2="32" stroke="var(--border)" stroke-width="1.5"/><line x1="24" y1="16" x2="37" y2="32" stroke="var(--border)" stroke-width="1.5"/></svg></div><p class="empty-title">No Parse Tree Yet</p><p class="empty-sub">Click "Generate Parse Tree" to visualize the grammar structure</p></div>`;

  derivHeader.style.display  = 'none';
  treeToolbar.style.display  = 'none';
  rulesTrace.style.display   = 'none';
  rulesTrace.innerHTML       = '';
  treeRulesTrace.style.display = 'none';
  treeRulesTrace.innerHTML     = '';
  derivExplainer.style.display = 'none';
  derivExplainer.innerHTML = '';
  treeExplainer.style.display = 'none';
  treeExplainer.innerHTML = '';

  renderParsedRules(null);
  setStatus('idle', 'Enter a grammar and string, then click a derivation button to begin.');
  showToast('Cleared');
}

/* ──────────────────────────────────────────
   EXAMPLE GRAMMARS
────────────────────────────────────────── */

const EXAMPLES = [
  {
    name:    'Simple Expression',
    grammar: 'S -> a S b\nS -> c',
    string:  'a a c b b',
    start:   'S',
  },
  {
    name:    'Arithmetic Expressions',
    grammar: 'E -> E + T | T\nT -> T * F | F\nF -> id | ( E )',
    string:  'id + id * id',
    start:   'E',
  },
  {
    name:    'Palindrome aⁿbⁿ',
    grammar: 'S -> a S b | ε',
    string:  'a a b b',
    start:   'S',
  },
  {
    name:    'CYK Example',
    grammar: 'S -> AB | BC\nA -> BA | a\nB -> CC | b\nC -> AB | a',
    string:  'b a a b a',
    start:   'S',
  },
  {
    name:    'Balanced Parens',
    grammar: 'S -> S S | ( S ) | ε',
    string:  '( ) ( )',
    start:   'S',
  },
  {
    name:    'Equal a and b Count',
    grammar: 'S -> a S b | ε',
    string:  'a a a b b b',
    start:   'S',
  },
  {
    name:    'Binary Strings',
    grammar: 'S -> 0 S | 1 S | ε',
    string:  '1 0 1 1 0',
    start:   'S',
  },
  {
    name:    'Identifier List',
    grammar: 'L -> id | id , L',
    string:  'id , id , id',
    start:   'L',
  },
  {
    name:    'Single Pair Parens',
    grammar: 'S -> ( S ) | a',
    string:  '( ( a ) )',
    start:   'S',
  },
  {
    name:    'Simple Assignment',
    grammar: 'S -> id = E\nE -> E + T | T\nT -> id | num',
    string:  'id = id + num',
    start:   'S',
  },
  {
    name:    'aaab Language',
    grammar: 'S -> a S | B\nB -> b',
    string:  'a a a b',
    start:   'S',
  },
  {
    name:    'Palindromic Core',
    grammar: 'S -> a S a | b S b | a | b | ε',
    string:  'a b b a',
    start:   'S',
  },
  {
    name:    'Impossible: Unequal a and b',
    grammar: 'S -> a S b | ε',
    string:  'a a b',
    start:   'S',
  },
  {
    name:    'Impossible: Unbalanced Parentheses',
    grammar: 'S -> S S | ( S ) | ε',
    string:  '( ( )',
    start:   'S',
  },
];

let exampleIdx = 0;

function loadExample() {
  const ex = EXAMPLES[exampleIdx % EXAMPLES.length];
  exampleIdx++;

  grammarInput.value = ex.grammar;
  stringInput.value  = ex.string;
  startSymbol.value  = ex.start;

  // Trigger grammar update
  const grammar = parseGrammar(ex.grammar);
  state.grammar = grammar;
  renderParsedRules(grammar);

  showToast(`Loaded: ${ex.name}`);
}

/* ──────────────────────────────────────────
   LIVE GRAMMAR PARSING
────────────────────────────────────────── */

let grammarDebounce;
grammarInput.addEventListener('input', () => {
  clearTimeout(grammarDebounce);
  grammarDebounce = setTimeout(() => {
    const grammar = parseGrammar(grammarInput.value);
    state.grammar = grammar;
    renderParsedRules(grammar);
  }, 300);
});

/* ──────────────────────────────────────────
   EVENT LISTENERS
────────────────────────────────────────── */

$('btn-leftmost').addEventListener('click',  doLeftmostDerivation);
$('btn-rightmost').addEventListener('click', doRightmostDerivation);
$('btn-tree').addEventListener('click',      doParseTree);
$('btn-clear').addEventListener('click',     clearAll);
$('example-btn').addEventListener('click',   loadExample);

// Tabs
$$('.tab-btn').forEach(btn => {
  btn.addEventListener('click', () => switchTab(btn.dataset.tab));
});

// Zoom
$('zoom-in').addEventListener('click',    () => setZoom(state.zoom + 0.15));
$('zoom-out').addEventListener('click',   () => setZoom(state.zoom - 0.15));
$('zoom-reset').addEventListener('click', () => setZoom(1));

// Export
$('export-btn').addEventListener('click', exportPNG);

// Replay
$('replay-btn').addEventListener('click', () => {
  if (!state.grammar || !state.derivationSteps.length) return;
  renderDerivationSteps(state.derivationSteps,
    derivTypeBadge.textContent.toLowerCase(),
    state.grammar);
});

// Theme toggle
$('theme-toggle').addEventListener('click', () => {
  const html    = document.documentElement;
  const current = html.dataset.theme || 'dark';
  html.dataset.theme = current === 'dark' ? 'light' : 'dark';
  showToast(current === 'dark' ? '☀️  Light theme' : '🌙  Dark theme');
});

// Keyboard shortcut: Enter in string input
stringInput.addEventListener('keydown', e => {
  if (e.key === 'Enter') doLeftmostDerivation();
});

/* ──────────────────────────────────────────
   INIT — Load first example on start
────────────────────────────────────────── */
window.addEventListener('DOMContentLoaded', () => {
  // Silently pre-fill the CYK example
  const ex = EXAMPLES[3];
  grammarInput.value = ex.grammar;
  stringInput.value  = ex.string;
  startSymbol.value  = ex.start;
  const grammar = parseGrammar(ex.grammar);
  state.grammar = grammar;
  renderParsedRules(grammar);
});
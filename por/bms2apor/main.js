'use strict';

// ---- UI 状態 (localStorage)
const KEY = 'bms2apor-ui';
let state = {};
try { state = JSON.parse(localStorage.getItem(KEY) || '{}'); } catch (e) { state = {}; }
function save(patch) {
  Object.assign(state, patch);
  try { localStorage.setItem(KEY, JSON.stringify(state)); } catch (e) { /* ignore */ }
}

const $ = id => document.getElementById(id);
const bmsEl = $('bms'), aporEl = $('apor');
const optDark = $('opt-dark');
const menuBtn = $('menu-btn'), menuPanel = $('menu-panel');

// ---- dark mode (default: on)
function applyDark(on) {
  document.documentElement.classList.toggle('dark', on);
  document.documentElement.classList.toggle('light', !on);
  optDark.checked = on;
}
applyDark(state.dark ?? true);
optDark.addEventListener('change', () => { applyDark(optDark.checked); save({ dark: optDark.checked }); });

// ---- menu
menuBtn.addEventListener('click', e => {
  e.stopPropagation();
  const open = menuPanel.hidden;
  menuPanel.hidden = !open;
  menuBtn.setAttribute('aria-expanded', String(open));
});
document.addEventListener('click', e => {
  if (!menuPanel.hidden && !menuPanel.contains(e.target)) {
    menuPanel.hidden = true;
    menuBtn.setAttribute('aria-expanded', 'false');
  }
});

// ---- 変換（ダミー）
function convert() {
  const lines = bmsEl.value.split('\n');
  aporEl.value = lines.map(line => line.trim() === '' ? '' : '(dummy) not implemented yet').join('\n');
}

// ---- URL query
function updateQuery() {
  const url = new URL(location.href);
  if (bmsEl.value === '') url.searchParams.delete('bms');
  else url.searchParams.set('bms', bmsEl.value);
  history.replaceState(null, '', url);
}

bmsEl.addEventListener('input', () => { convert(); updateQuery(); });

(function init() {
  const q = new URL(location.href).searchParams.get('bms');
  if (q !== null) bmsEl.value = q;
  convert();
})();

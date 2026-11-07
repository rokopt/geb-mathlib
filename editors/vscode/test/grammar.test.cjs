const assert = require('node:assert/strict');
const { readFileSync } = require('node:fs');
const path = require('node:path');
const { test, before } = require('node:test');
const { Registry, parseRawGrammar, INITIAL } = require('vscode-textmate');
const { loadWASM, OnigScanner, OnigString } = require('vscode-oniguruma');

let grammar;
before(async () => {
  await loadWASM(readFileSync(require.resolve('vscode-oniguruma/release/onig.wasm')));
  const file = path.join(__dirname, '../syntaxes/geb.tmLanguage.json');
  const registry = new Registry({
    onigLib: Promise.resolve({
      createOnigScanner: patterns => new OnigScanner(patterns),
      createOnigString: text => new OnigString(text),
    }),
    loadGrammar: async () => parseRawGrammar(readFileSync(file, 'utf8'), file),
  });
  grammar = await registry.loadGrammar('source.geb');
});

function tokens(text) {
  let state = INITIAL;
  return text.split(/\r?\n/).flatMap(line => {
    const result = grammar.tokenizeLine(line, state);
    state = result.ruleStack;
    return result.tokens.map(t => ({
      text: line.slice(t.startIndex, t.endIndex), scopes: t.scopes,
    }));
  });
}

test('comments and quoted atoms hide their parentheses from bracket matching', () => {
  const text = '(quote (0 "(; \\"quoted\\")")) ; ( ] } "';
  const ts = tokens(text);
  assert.equal(ts.filter(t => t.scopes.includes('punctuation.section.parens.geb'))
    .map(t => t.text).join(''), '(())');
  assert.ok(ts.some(t => t.scopes.includes('constant.character.escape.geb')));
  assert.ok(ts.at(-1).scopes.includes('comment.line.semicolon.geb'));
});

test('multiline and unfinished quoted atoms retain string scope', () => {
  const ts = tokens('(def "λ" "first\r\n(; second\r\nunfinished');
  assert.ok(ts.at(-1).scopes.includes('string.quoted.double.geb'));
  assert.equal(ts.filter(t => t.scopes.includes('comment.line.semicolon.geb')).length, 0);
});

test('holes, numerals and rest markers are distinct from qualified names', () => {
  const ts = tokens('(?goal Label.app23 123 & "?literal")');
  assert.equal(ts.find(t => t.text === '?goal').scopes.at(-1), 'variable.other.hole.geb');
  assert.equal(ts.find(t => t.text === '123').scopes.at(-1), 'constant.numeric.geb');
  assert.equal(ts.find(t => t.text === '&').scopes.at(-1), 'keyword.operator.rest.geb');
  assert.equal(ts.find(t => t.text.includes('Label.app23')).scopes.at(-1), 'source.geb');
});

test('the authoring fixture tokenizes with LF and CRLF identically', () => {
  const text = readFileSync(path.join(__dirname, 'fixtures/profile.geb'), 'utf8');
  assert.deepEqual(tokens(text), tokens(text.replaceAll('\n', '\r\n')));
  assert.equal(tokens(text).at(-1).scopes.at(-1), 'source.geb');
});

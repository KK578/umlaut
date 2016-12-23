const parsey = require('parsey');

const Sym = parsey.Sym;
const Rule = parsey.Rule;

const smtResult = new Sym('smtResult');
const identifier = new Sym('identifier');
const inputValue = new Sym('inputValue');

const grammar = [
	new Rule(smtResult, ['(', identifier, inputValue, ')'], (_, id, v, __) => {
		const result = { [id]: v };

		return result;
	}),

	new Rule(identifier, [/[a-zA-Z]+/], (name) => {
		return name;
	}),

	new Rule(inputValue, [/[0-9]+/], (v) => {
		return v;
	})
];

const parsed = parsey.parse(`(a 0)`, grammar);

function interpret(parseTree) {
  if (typeof parseTree === 'string' || parseTree == null) {
    return parseTree;
  }

  let values = parseTree.children
    .map((tree) => interpret(tree))
    .filter((value) => value != null);

  return parseTree.item.evaluate(values);
}

console.log(parsed);
console.log('-----');
console.log(parsed.children);
console.log('-----');
console.log(interpret(parsed));

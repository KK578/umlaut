const parsey = require('parsey');

const Sym = parsey.Sym;
const Rule = parsey.Rule;

/**
 * CFG for results from get-value of SMT-LIB2 run through z3.
 *
 * 	smtResult	::= '(' smtValue ')'
 *
 * 	smtValue	::= '(' identifier WHITESPACE inputValue ')'
 * 					| smtValue WHITESPACE '(' identifier WHITESPACE inputValue ')'
 *
 * 	identifier	::=	[a-zA-Z_][a-zA-Z0-9_]*
 *
 * 	inputValue	::= [0-9]+
 */
const smtResult = new Sym('smtResult');
const smtValue = new Sym('smtValue');
const identifier = new Sym('identifier');
const inputValue = new Sym('inputValue');

const grammar = [
	new Rule(smtResult, ['(', smtValue, ')'], (_, values, __) => {
		return values;
	}),

	new Rule(smtValue, [smtValue, '(', identifier, inputValue, ')'], (next, _, id, v, __) => {
		let result = { [id]: v };
		result = Object.assign(next, result);

		return result;
	}),
	new Rule(smtValue, ['(', identifier, inputValue, ')'], (_, id, v, __) => {
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

const parsed = parsey.parse(`((a 0)(b 1)(c 5))`, grammar);

// Note: From parsey/examples/calc.
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

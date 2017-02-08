const parsey = require('parsey');

const Sym = parsey.Sym;
const Rule = parsey.Rule;

const comparisons = require('../../../util/comparisons.js');

/**
 * CFG for conditions annotated on UML models.
 *
 * condition	::= '(' comparison argumentList ')'
 *
 * argumentList	::= argumentList argument
 * 					| argument
 *
 * argument		::= [_a-zA-Z][-_a-zA-Z0-9]*
 *
 * exception	::= 'Exception' ':' argument
 */
const conditionList = new Sym('conditionList');
const condition = new Sym('condition');
const comparison = new Sym('comparison');
const argumentList = new Sym('argumentList');
const argument = new Sym('argument');
const exception = new Sym('exception');

const grammar = [
	new Rule(conditionList, [conditionList, ',', condition], (next, _, c) => {
		return next.concat(c);
	}),
	new Rule(conditionList, [condition], (c) => {
		return c;
	}),

	new Rule(condition, ['(', argument, comparison, argument, exception, ')'], (_, a1, c, a2, e) => {
		return [{
			comparison: c,
			arguments: [a1, a2],
			exception: e
		}];
	}),
	new Rule(condition, ['(', argument, comparison, argument, ')'], (_, a1, c, a2) => {
		return [{
			comparison: c,
			arguments: [a1, a2]
		}];
	}),

	new Rule(comparison, [/[<>=]+/], (c) => {
		const foundComparison = comparisons.toName(c);

		if (foundComparison !== false) {
			return foundComparison;
		}
		else {
			throw new Error(`Comparison ${c} does not exist.`);
		}
	}),

	new Rule(argumentList, [argumentList, argument], (next, a) => {
		return next.concat(a);
	}),
	new Rule(argumentList, [argument], (a) => {
		return [a];
	}),

	new Rule(argument, [/[a-zA-Z_][-_a-zA-Z0-9]*/], (a) => {
		return a;
	}),
	new Rule(argument, [/-?[0-9]+/], (a) => {
		return parseInt(a);
	}),

	new Rule(exception, ['Exception', ':', /[a-zA-Z_][-_a-zA-Z0-9]*/], (_, __, e) => {
		return e;
	})
];

// Note: From parsey/examples/calc.
function interpret(parseTree) {
	if (typeof parseTree === 'string' || parseTree === null || parseTree === undefined) {
		return parseTree;
	}

	const values = parseTree.children
		.map(interpret)
		.filter((value) => {
			return !(value === null || value === undefined);
		});

	return parseTree.item.evaluate(values);
}

function parse(input) {
	const parsed = parsey.parse(input, grammar);

	return interpret(parsed);
}

module.exports = parse;

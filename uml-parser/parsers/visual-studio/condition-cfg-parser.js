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
const comparisonSymbol = new Sym('comparisonSymbol');
const argumentList = new Sym('argumentList');
const argument = new Sym('argument');
const linked = new Sym('linked');
const linkedConditionList = new Sym('linkedConditionList');
const exception = new Sym('exception');

const comparisonGrammars = comparisons.map((c) => {
	return new Rule(comparisonSymbol, [c.symbol], () => {
		return c.name;
	});
});

const grammar = [
	new Rule(conditionList, [conditionList, ',', condition], (next, _, c) => {
		return next.concat(c);
	}),
	new Rule(conditionList, [condition], (c) => {
		return c;
	}),

	new Rule(condition, ['(', linked, comparison, exception, ')'], (_, l, c, e) => {
		c.linkedPreconditions = l;
		c.exception = e;

		return [c];
	}),
	new Rule(condition, ['(', comparison, exception, ')'], (_, c, e) => {
		c.exception = e;

		return [c];
	}),
	new Rule(condition, ['(', linked, comparison, ')'], (_, l, c) => {
		c.linkedPreconditions = l;

		return [c];
	}),
	new Rule(condition, ['(', comparison, ')'], (_, c) => {
		return [c];
	}),

	new Rule(comparison, [argument, comparisonSymbol, argument], (a1, c, a2) => {
		return {
			comparison: c,
			arguments: [a1, a2]
		};
	}),

	new Rule(linked, ['{', linkedConditionList, '}'], (_, l) => {
		return l;
	}),
	new Rule(linkedConditionList, [/[0-9]+/, ',', linkedConditionList], (n, _, n2) => {
		return [n, ...n2];
	}),
	new Rule(linkedConditionList, [/[0-9]+/], (n) => {
		return [n];
	}),

	// All comparisons are listed here
	...comparisonGrammars,

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

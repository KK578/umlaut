const parsey = require('parsey');

const Sym = parsey.Sym;
const Rule = parsey.Rule;

const comparisons = require('../../../util/comparisons.json');

function checkValidComparison(comparison) {
	for (let i = 0; i < comparisons.length; i++) {
		if (comparisons[i].name === comparison) {
			return comparison;
		}

		if (comparisons[i].symbol === comparison) {
			return comparisons[i].name;
		}
	}

	// DEBUG
	if (comparison === '=') {
		return '==';
	}
	// END DEBUG

	return false;
}

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
const condition = new Sym('condition');
const comparison = new Sym('comparison');
const argumentList = new Sym('argumentList');
const argument = new Sym('argument');
const exception = new Sym('exception');

const grammar = [
	new Rule(condition, ['(', comparison, argumentList, exception, ')'], (_, c, a, e) => {
		return {
			comparison: c,
			arguments: a,
			exception: e
		};
	}),
	new Rule(condition, ['(', comparison, argumentList, ')'], (_, c, a) => {
		return {
			comparison: c,
			arguments: a
		};
	}),

	new Rule(comparison, [/[a-zA-Z]+/], (c) => {
		const foundComparison = checkValidComparison(c);

		if (foundComparison !== false) {
			return foundComparison;
		}
		else {
			throw new Error(`Comparison ${c} does not exist.`);
		}
	}),
	// DEBUG
	new Rule(comparison, [/[a-zA-Z<>=!&|]+/], (c) => {
		const foundComparison = checkValidComparison(c);

		if (foundComparison !== false) {
			return foundComparison;
		}
		else {
			throw new Error(`Comparison ${c} does not exist.`);
		}
	}),
	// END DEBUG

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
	if (typeof parseTree === 'string' || (parseTree === null || parseTree === undefined)) {
		return parseTree;
	}

	const values = parseTree.children
		.map(interpret)
		.filter((value) => {
			const result = !(value === null || value === undefined);

			return result;
		});

	return parseTree.item.evaluate(values);
}

function parse(input) {
	const parsed = parsey.parse(input, grammar);

	return interpret(parsed);
}

module.exports = parse;

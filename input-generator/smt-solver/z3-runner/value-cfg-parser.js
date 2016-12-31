const parsey = require('parsey');

const Sym = parsey.Sym;
const Rule = parsey.Rule;

/**
 * CFG for results from get-value of SMT-LIB2 run through z3.
 *
 * 	smtResult	::= '(' smtValue ')'
 * 					;
 *
 * 	smtValue	::= '(' identifier WHITESPACE inputValue ')'
 * 					| smtValue WHITESPACE '(' identifier WHITESPACE inputValue ')'
 * 					;
 *
 * 	identifier	::=	[a-zA-Z_][-_a-zA-Z0-9]*
 * 					;
 *
 * 	inputValue	::= numericValue
 * 					;
 *
 * 	numericValue	::= '(' '-' numericValue2 ')'
 * 						| numericValue2
 * 						;
 *
 *  numericValue2	::= [0-9]+
 */
const smtIdResult = new Sym('smtIdResult');
const conditionId = new Sym('conditionId');
const smtResult = new Sym('smtResult');
const smtValue = new Sym('smtValue');
const identifier = new Sym('identifier');
const inputValue = new Sym('inputValue');
const numericValue = new Sym('numericValue');
const numericValue2 = new Sym('numericValue2');

const UUID_REGEX = /[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}/i;

const grammar = [
	// smtIdResult
	new Rule(smtIdResult, ['[[', conditionId, ']]', 'sat', smtResult], (_, id, __, ___, values) => {
		return {
			id,
			values
		};
	}),

	// conditionId
	new Rule(conditionId, [/Valid/], (id) => {
		return id;
	}),
	new Rule(conditionId, [UUID_REGEX], (id) => {
		return id;
	}),

	// smtResult
	new Rule(smtResult, ['(', smtValue, ')'], (_, values) => {
		return values;
	}),

	// smtValue
	new Rule(smtValue, [smtValue, '(', identifier, inputValue, ')'], (next, _, id, v) => {
		let result = { [id]: v };

		result = Object.assign(next, result);

		return result;
	}),
	new Rule(smtValue, ['(', identifier, inputValue, ')'], (_, id, v) => {
		const result = { [id]: v };

		return result;
	}),

	// identifier
	new Rule(identifier, [/[a-zA-Z_][-_a-zA-Z0-9]*/], (name) => {
		return name;
	}),

	// inputValue
	new Rule(inputValue, [numericValue], (v) => {
		return v;
	}),

	// numericValue
	new Rule(numericValue, ['(', '-', numericValue2, ')'], (_, __, v) => {
		return -1 * v;
	}),
	new Rule(numericValue, [numericValue2], (v) => {
		return v;
	}),

	// numericValue2
	new Rule(numericValue2, [/[0-9]+/], (v) => {
		return parseInt(v);
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

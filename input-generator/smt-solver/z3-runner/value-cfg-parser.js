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
const parsey = require('parsey');

const Sym = parsey.Sym;
const Rule = parsey.Rule;

// Parsey symbols
const smtInputsList = new Sym('smtInputsList');
const smtTest = new Sym('smtTest');
const conditionIdentifier = new Sym('conditionIdentifier');
const smtError = new Sym('smtError');
const ignoredStrings = new Sym('ignoredStrings');
const smtInputs = new Sym('smtInputs');
const smtValues = new Sym('smtValues');
const identifier = new Sym('identifier');
const inputValue = new Sym('inputValue');
const numericValue = new Sym('numericValue');
const numericValue2 = new Sym('numericValue2');

const UUID_REGEX = /[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}/i;

const grammar = [
	// smtIdResultList
	new Rule(smtInputsList, [smtInputsList, '\\', smtTest], (next, _, values) => {
		return next.concat(values);
	}),
	new Rule(smtInputsList, [smtTest], (values) => {
		return [values];
	}),

	// smtIdResult
	new Rule(smtTest, ['[[', conditionIdentifier, ']]', 'sat', smtInputs], (_, id, __, ___, values) => {
		return {
			id,
			values
		};
	}),
	new Rule(smtTest, ['[[', conditionIdentifier, ']]', 'unsat', smtError], (_, id) => {
		return {
			id,
			unsatisfiable: true
		};
	}),

	// conditionId
	new Rule(conditionIdentifier, [/Valid/], (id) => {
		return id;
	}),
	new Rule(conditionIdentifier, [UUID_REGEX], (id) => {
		return id;
	}),

	// smtError
	new Rule(smtError, ['(', 'error', ignoredStrings, ')'], () => {
		return null;
	}),

	// ignoredStrings
	new Rule(ignoredStrings, [/[a-zA-Z0-9"':]+/, ignoredStrings], () => {
		return null;
	}),
	new Rule(ignoredStrings, [/[a-zA-Z0-9"':]+/], () => {
		return null;
	}),


	// smtResult
	new Rule(smtInputs, ['(', smtValues, ')'], (_, values) => {
		return values;
	}),

	// smtValue
	new Rule(smtValues, [smtValues, '(', identifier, inputValue, ')'], (next, _, id, v) => {
		let result = { [id]: v };

		result = Object.assign(next, result);

		return result;
	}),
	new Rule(smtValues, ['(', identifier, inputValue, ')'], (_, id, v) => {
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

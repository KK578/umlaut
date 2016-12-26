const parser = require('./value-cfg-parser.js');

function parseValues(text) {
	return parser(text);
}

function parseCondition(text) {
	const split = text.split('\n');
	const condition = split[0];
	let args = {};

	if (split[1] === 'sat') {
		const values = split.slice(2).join('');

		args = parseValues(values);
	}
	else {
		args = 'Unsatisfiable';
	}

	return {
		condition,
		args
	};
}

function parse(text) {
	let split = text.split('-----');

	// Ignore first as it will be empty.
	split = split.slice(1);

	const results = split.map(parseCondition);

	return results;
}

module.exports = parse;

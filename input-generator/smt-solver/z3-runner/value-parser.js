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
		arguments: args
	};
}

function parse(text) {
	return parser(text);
}

module.exports = parse;

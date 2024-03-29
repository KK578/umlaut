const parsers = [
	require('./visual-studio/index.js')
];

function promiseParse(data, parserCount) {
	if (parserCount >= parsers.length) {
		throw new Error('No valid parser found.');
	}

	const parser = parsers[parserCount];

	return Promise.resolve(parser.detect(data)).then((valid) => {
		if (valid) {
			// Parser has claimed it can parse the model.
			// If this errors, this will throw to the catch and proceed to the next parser.
			return parser.parse(data);
		}
		else {
			// Throw error to go to next parser.
			throw new Error();
		}
	}).catch(() => {
		return promiseParse(data, parserCount + 1);
	});
}

function parse(umlData) {
	return promiseParse(umlData, 0);
}

module.exports = {
	parse
};

const parsers = [
	require('./visual-studio/index.js')
];

function promiseParse(data, parserCount) {
	if (parserCount > parsers.length) {
		return false;
	}

	const parser = parsers[parserCount];

	return parser.detect(data).catch((error) => {
		return false;
	}).then((valid) => {
		if (valid) {
			return parser.parse(data);
		}
		else {
			return false;
		}
	});
}

function parse(umlData) {
	return promiseParse(umlData, 0);
}

module.exports = {
	parse
};

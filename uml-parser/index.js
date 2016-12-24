const promises = require('../util/promises.js');

const parser = require('./parsers/parser.js');

module.exports = (filePath) => {
	return promises.fsReadFile(filePath).then((data) => {
		return parser.parse(data);
	}).catch((error) => {
		throw error;
	});
};

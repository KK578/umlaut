const fs = require('fs');

const parser = require('./parsers/parser.js');

function promiseFsReadFile(filename) {
	return new Promise((resolve, reject) => {
		fs.readFile(filename, 'utf-8', (err, data) => {
			if (err) {
				reject(err);
			}
			else {
				resolve(data);
			}
		});
	});
}

module.exports = (filePath) => {
	return promiseFsReadFile(filePath).then((data) => {
		return parser.parse(data);
	}).catch((error) => {
		throw error;
	});
};

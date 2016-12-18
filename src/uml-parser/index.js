const fs = require('fs');
const path = require('path');
const xml2js = require('xml2js');
const xmlParser = new xml2js.Parser();

const parser = require('./parsers/parser.js');

module.exports = (filePath) => {
	fs.readFile(filePath, (err, data) => {
		if (err) {
			throw err;
		}

		// TODO: Enable parsing other structure types.
		xmlParser.parseString(data, (err, uml) => {
			if (err) {
				throw err;
			}

			const parsed = parser.parse(uml);

			Object.keys(parsed).map((className) => {
				const output = JSON.stringify(parsed[className], null, 2);
				const outputFile = `${className}.json`;

				fs.writeFile(path.join(__dirname, `../../build/uml/${outputFile}`), output, 'utf-8');
			});
		});
	});
};

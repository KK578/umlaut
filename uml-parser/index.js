const fs = require('fs');
const path = require('path');
const xml2js = require('xml2js');
const xmlParser = new xml2js.Parser();

const parser = require('./util/parser.js');

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
			const output = JSON.stringify(parsed, null, 2);

			fs.writeFile(path.join(__dirname, '../build/SimpleMath.json'), output, 'utf-8');
		});
	});
};

const fs = require('fs');
const path = require('path');
const xml2js = require('xml2js');
const xmlParser = new xml2js.Parser();

const parser = require('./util/parser.js');

{
	const filePath = path.resolve(process.cwd(), process.argv[2]);

	fs.readFile(filePath, (err, data) => {
		if (err) {
			throw err;
		}

		xmlParser.parseString(data, (err, uml) => {
			if (err) {
				throw err;
			}

			parser.parse(uml);
		});
	});
}

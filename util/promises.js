const fs = require('fs');
const xml2js = require('xml2js');

function fsReadFile(filename) {
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

function xmlParseString(xml) {
	return new Promise((resolve, reject) => {
		const xmlParser = new xml2js.Parser();

		xmlParser.parseString(xml, (err, data) => {
			if (err) {
				reject(err);
			}
			else {
				resolve(data);
			}
		});
	});
}

module.exports = {
	fsReadFile,
	xmlParseString
};

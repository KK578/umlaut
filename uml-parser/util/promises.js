const xml2js = require('xml2js');

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
	xmlParseString
};

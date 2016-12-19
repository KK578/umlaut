const xml2js = require('xml2js');

function promiseXmlParseString(xml) {
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

module.exports = (data) => {
	return promiseXmlParseString(data).then((xml) => {
		if (xml.modelStoreModel !== undefined) {
			// Contains elements that hint towards a UML model made in Visual Studio.
			// TODO: More validation?
			return true;
		}
		else {
			return false;
		}
	}).catch((error) => {
		// Failed to indicate the file was XML -> Not Visual Studio UML model.
		return false;
	});
};

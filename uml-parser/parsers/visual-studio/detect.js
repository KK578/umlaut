const promises = require('../../util/promises.js');

module.exports = (data) => {
	return promises.xmlParseString(data).then((xml) => {
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

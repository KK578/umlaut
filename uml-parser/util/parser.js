const parsers = {
	visualStudio: require('./parserVisualStudio.js')
};

function parse(umlData) {
	let parser;

	if (umlData.modelStoreModel) {
		// Probably Visual Studio Modeling File.
		parser = parsers.visualStudio;
	}

	const classes = parser(umlData);

	return classes;
}

module.exports = {
	parse
};

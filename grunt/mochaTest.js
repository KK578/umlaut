module.exports = {
	options: {
		reporter: 'spec',
		require: ['./test/config/globals.js']
	},
	'all': { src: 'test/test-suite.js' },
	'uml-parser': { src: 'test/uml-parser/test-suite.js' },
	'input-generator': { src: 'test/input-generator/test-suite.js' },
	'test-generator': { src: 'test/test-generator/test-suite.js' }
};

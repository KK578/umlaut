module.exports = {
	options: { reporter: 'spec', slow: 1000 },
	'all': {
		src: [
			'test/*/*-test.js',
			'test/*-test.js'
		]
	},
	'uml-parser': { src: 'test/uml-parser/*-test.js' },
	'input-generator': { src: 'test/input-generator/*-test.js' },
	'test-generator': { src: 'test/test-generator/*-test.js' }
};

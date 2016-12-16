module.exports = {
	options: {
		reporter: 'spec',
		reportFormats: ['lcovonly']
	},
	'all': { src: 'test/*/*-test.js' },
	'html': {
		options: {
			reportFormats: ['lcov']
		},
		src: 'test/*/*-test.js'
	},
	'uml-parser': { src: 'test/uml-parser/*-test.js' },
	'smt-generator': { src: 'test/smt-generator/*-test.js' },
	'test-generator': { src: 'test/test-generator/*-test.js' }
};

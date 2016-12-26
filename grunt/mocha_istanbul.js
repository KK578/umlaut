module.exports = {
	options: {
		reporter: 'spec',
		reportFormats: ['lcovonly']
	},
	'all': {
		src: [
			'test/*/*-test.js',
			'test/*-test.js'
		]
	},
	'html': {
		options: {
			reportFormats: ['lcov']
		},
		src: [
			'test/*/*-test.js',
			'test/*-test.js'
		]
	},
	'uml-parser': { src: 'test/uml-parser/*-test.js' },
	'input-generator': { src: 'test/input-generator/*-test.js' },
	'test-generator': { src: 'test/test-generator/*-test.js' }
};

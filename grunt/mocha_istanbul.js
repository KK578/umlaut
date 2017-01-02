module.exports = {
	options: {
		reporter: 'spec',
		reportFormats: ['lcovonly'],
		require: ['./test/config/globals.js']
	},
	html: {
		options: {
			reportFormats: ['lcov']
		},
		src: 'test/test-suite.js'
	},
	'uml-parser': {
		options: { coverageFolder: 'coverage/uml-parser/' },
		src: 'test/uml-parser/test-suite.js'
	},
	'input-generator': {
		options: { coverageFolder: 'coverage/input-generator/' },
		src: 'test/input-generator/test-suite.js'
	},
	'test-generator': {
		options: { coverageFolder: 'coverage/test-generator/' },
		src: 'test/test-generator/test-suite.js'
	}
};

module.exports = {
	default: {
		tasks: [
			'lint',
			'test'
		]
	},
	lint: {
		description: 'Lint files in the project.',
		tasks: [
			'eslint'
		]
	},
	test: ['mochaTest'],
	coverage: [
		'mocha_istanbul:uml-parser',
		'mocha_istanbul:input-generator',
		'mocha_istanbul:test-generator'
	]
};

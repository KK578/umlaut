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
	test: ['mochaTest:all'],
	coverage: ['mocha_istanbul:all']
};

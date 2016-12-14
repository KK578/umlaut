module.exports = {
	default: {
		tasks: [
			'lint',
			'mochaTest:all'
		]
	},
	lint: {
		description: 'Lint files in the project.',
		tasks: [
			'eslint'
		]
	}
};

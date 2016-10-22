module.exports = {
	default: {
		tasks: [
			'lint',
			'mochaTest'
		]
	},
	lint: {
		description: 'Lint files in the project.',
		tasks: [
			'eslint'
		]
	}
};

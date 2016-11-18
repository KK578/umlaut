module.exports = {
	options: {
		format: 'node_modules/eslint-formatter-pretty'
	},
	project: {
		files: [
			{
				expand: true,
				src: [
					'gruntfile.js',
					'grunt/*.js',
					'scripts/*.js'
				]
			}
		]
	},
	'smt-generator': {
		files: [
			{
				expand: true,
				src: [
					'smt-generator/**/*.js',
					'!smt-generator/node_modules/**/*.js'
				]
			}
		]
	},
	'uml-parser': {
		files: [
			{
				expand: true,
				src: [
					'uml-parser/**/*.js',
					'!uml-parser/node_modules/**/*.js'
				]
			}
		]
	}
};

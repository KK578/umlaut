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
					'test/*.js',
					'util/*.js'
				]
			}
		]
	},
	'smt-generator': {
		files: [
			{
				expand: true,
				src: [
					'src/smt-generator/**/*.js'
				]
			}
		]
	},
	'uml-parser': {
		files: [
			{
				expand: true,
				src: [
					'src/uml-parser/**/*.js'
				]
			}
		]
	},
	'test-generator': {
		files: [
			{
				expand: true,
				src: [
					'src/test-generator/**/*.js'
				]
			}
		]
	}
};

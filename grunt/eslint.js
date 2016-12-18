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
					'util/*.js'
				]
			}
		]
	},
	'input-generator': {
		files: [
			{
				expand: true,
				src: [
					'src/input-generator/**/*.js',
					'test/input-generator/*.js'
				]
			}
		]
	},
	'uml-parser': {
		files: [
			{
				expand: true,
				src: [
					'src/uml-parser/**/*.js',
					'test/uml-parser/*.js'
				]
			}
		]
	},
	'test-generator': {
		files: [
			{
				expand: true,
				src: [
					'generators/**/*.js',
					'test/test-generator/*.js'
				]
			}
		]
	}
};

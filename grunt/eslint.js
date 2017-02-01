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
					'util/*.js',
					'test/*.js',
					'test/{config,uml-parser,input-generator,test-generator}/**/*.js'
				]
			}
		]
	},
	'input-generator': {
		files: [
			{
				expand: true,
				src: ['input-generator/**/*.js']
			}
		]
	},
	'uml-parser': {
		files: [
			{
				expand: true,
				src: ['uml-parser/**/*.js']
			}
		]
	},
	'test-generator': {
		files: [
			{
				expand: true,
				src: [
					'generators/**/*.js',
					'!generators/*/templates/*.js'
				]
			}
		]
	}
};

const Generator = require('yeoman-generator');

function getLanguageType(type) {
	if (type === '#SelfReference') {
		// Do not overwrite special types used in the tool.
		return type;
	}

	// TODO: Expand this to a config file lookup
	return 'var';
}

function convertTypes(method) {
	function convert(item) {
		item.type = getLanguageType(item.type);
	}

	method.tests.forEach((test) => {
		if (test) {
			test.initialise.forEach(convert);
			test.run.forEach(convert);
		}
	});
}

module.exports = class extends Generator {
	constructor(args, opts) {
		super(args, opts);

		this.option('classes', {
			type: String,
			desc: 'JSON object, or path to a JSON file, describing the model.'
		});
	}

	configuring() {
		this.classes = JSON.parse(this.options.classes);

		this.classes.forEach((c) => {
			c.methods.forEach(convertTypes);
		});
	}

	writing() {
		this.classes.forEach((c) => {
			const copyTpl = (source, destination, options) => {
				this.fs.copyTpl(this.templatePath(source),
					this.destinationPath(destination),
					options);
			};

			copyTpl('test-class.js', `build/${c.name}Test.js`, { classObject: c });
		});
	}
};

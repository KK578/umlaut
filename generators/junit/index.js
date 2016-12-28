const Generator = require('yeoman-generator');

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
	}

	writing() {
		this.classes.map((c) => {
			const copyTpl = (source, destination, options) => {
				this.fs.copyTpl(this.templatePath(source),
					this.destinationPath(destination),
					options);
			};

			copyTpl('test-class.java', `build/${c.name}Test.java`, { classObject: c });
		});
	}
};

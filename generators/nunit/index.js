const Generator = require('yeoman-generator');

function getLanguageType(type) {
	// TODO: Expand this to a config file lookup
	switch (type) {
		case 'Integer':
		case 'Int':
		case 'int':
			return 'int';

		default:
			console.log(`Undefined type "${type}"`);

			return type;
	}
}

function convertTypes(method) {
	function convert(item) {
		item.type = getLanguageType(item.type);
	}

	method.tests.map((test) => {
		if (test) {
			test.initialise.map(convert);
			test.run.map(convert);
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

		this.classes.map((c) => {
			c.methods.map(convertTypes);
		});
	}

	writing() {
		this.classes.map((c) => {
			const copyTpl = (source, destination, options) => {
				this.fs.copyTpl(this.templatePath(source),
					this.destinationPath(destination),
					options);
			};

			copyTpl('test-class.cs', `build/${c.name}Test.cs`, { classObject: c });
		});
	}
};

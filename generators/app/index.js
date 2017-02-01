const Generator = require('yeoman-generator');

const classToTests = require('./util/class-to-tests.js');

function parseModel(model) {
	let result = {};

	try {
		result = JSON.parse(model);
	}
	catch (err) {
		// Should attempt to load data from file here.
	}

	return result;
}

module.exports = class extends Generator {
	constructor(args, opts) {
		super(args, opts);

		this.option('model', {
			type: String,
			desc: 'JSON object, or path to a JSON file, describing the model.'
		});

		this.option('framework', {
			type: String,
			desc: 'Name of framework to build tests in.'
		});
	}

	prompting() {
		if (!this.options.framework) {
			return this.prompt([{
				type: 'list',
				name: 'framework',
				message: 'Test framework to build for',
				// TODO: Build this list dynamically.
				choices: [
					'junit',
					'nunit',
					'mocha'
				]
			}]).then((answers) => {
				this.options.framework = answers.framework;
			});
		}
	}

	initializing() {
		this.model = parseModel(this.options.model);
		this.classes = Object.keys(this.model).map((className) => {
			return classToTests(this.model[className]);
		});
	}

	configuring() {
		// TODO: Resolve directly from npm module name.
		const subGenerator = require.resolve(`../${this.options.framework}`);

		this.composeWith(subGenerator, {
			classes: JSON.stringify(this.classes)
		});
	}
};

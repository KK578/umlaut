const Generator = require('yeoman-generator');

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
	}

	initializing() {
		this.model = parseModel(this.options.model);
	}

	configuring() {
		console.log(this.model);
	}
};

const generators = require('yeoman-generator');

function parseModel(model) {
	try {
		const result = JSON.parse(model);
	}
	catch (err) {

	}
}

module.exports = generators.Base.extend({
	constructor: function () {
		generators.Base.apply(this, arguments);

		this.option('model', {
			type: String,
			desc: 'JSON object, or path to a JSON file, describing the model.',
		});
	},

	initializing() {
		this.model = parseModel(this.options.model);
	}
});

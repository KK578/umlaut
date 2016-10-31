const generators = require('yeoman-generator');

const path = require('path');

let uml;
let smt;
let methods = [];

const generator = generators.Base.extend({
	constructor: function () {
		generators.Base.apply(this, arguments);

		this.argument('umlFile', {
			type: String,
			description: 'Filepath for JSON describing the class',
			required: true
		});
		this.argument('smtFile', {
			type: String,
			description: 'Filepath for JSON describing solved SMT',
			required: true
		});
	},

	initializing(done) {
		uml = require(path.resolve(process.cwd(), this.umlFile));
		smt = require(path.resolve(process.cwd(), this.smtFile));
	},

	configuring() {
		methods = uml.methods.map((m) => {
			const method = {
				name: m.name,
				arguments: m.arguments,
				return: m.return,
				tests: smt[m.name]
			};

			return method;
		});

		console.log(JSON.stringify(methods, null, 2));
	}
});

module.exports = generator;

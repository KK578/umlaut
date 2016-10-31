const generators = require('yeoman-generator');

const path = require('path');

let uml;
let smt;
let methods = [];

function generateTestMethodName(methodName, condition) {
	const clean = condition.replace(/[<>=() \t]/g, '');

	return `test_${methodName}_${clean}`;
}

function getValue(arg, value) {
	let v = value;

	switch (arg.type) {
		case 'Int':
		case 'int':
			if (v[0] === '(') {
				v = v.slice(1, v.length - 1);
				v = v.replace(' ', '');
			}

			v = parseInt(v);
			break;

		default:
			break;
	}

	return v;
}

function generateArgumentString(methodArgs, testArgs) {
	const keys = Object.keys(testArgs);
	const values = keys.map((key) => {
		let value = testArgs[key];

		for (let i = 0; i < keys.length; i++) {
			if (methodArgs[i].name === key) {
				value = getValue(methodArgs[i], testArgs[key]);
			}
		}

		return value;
	});

	return values.join(', ');
}

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
			const tests = smt[m.name].map((t) => {
				if (t.args === 'Unsatisfiable') {
					return null;
				}

				const test = {
					name: generateTestMethodName(m.name, t.condition),
					args: t.args,
					argumentString: generateArgumentString(m.arguments, t.args)
				};

				return test;
			});

			const method = {
				name: m.name,
				arguments: m.arguments,
				return: m.return,
				tests: tests
			};

			return method;
		});

		// console.log(JSON.stringify(methods, null, 2));
	},

	writing() {
		this.template('test-class.cs', 'SimpleMath.cs', { method: methods[0] });
	}
});

module.exports = generator;

const generators = require('yeoman-generator');

const path = require('path');

let uml;
let smt;
const classes = [];

function comparatorString(comparator) {
	let value = '';

	switch (comparator) {
		case '=':
			value = 'Equal';
			break;

		case '<':
			value = 'LessThan';
			break;

		case '<=':
			value = 'LessThanOrEqual';
			break;

		case '>':
			value = 'GreaterThan';
			break;

		case '>=':
			value = 'GreaterThanOrEqual';
			break;

		case '&':
			value = 'And';
			break;

		case '|':
			value = 'Or';
			break;

		default:
			break;
	}

	return value;
}

function generateTestMethodName(method, testId) {
	let condition;
	let id = '';
	let clean;

	if (testId === 'Valid') {
		clean = 'Valid';
	}
	else {
		for (let i = 0; i < method.preconditions.length; i++) {
			const c = method.preconditions[i];

			if (c.id === testId) {
				condition = c;
				break;
			}
		}

		clean = `Not${comparatorString(condition.comparison)}_${condition.arguments.join('_')}`;
	}

	return `test_${method.name}_${clean}`;
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

function getLanguageType(type) {
	// TODO: Expand this to a config file lookup
	switch (type) {
		case 'Int':
		case 'int':
			return 'int';

		default:
			console.log(`Undefined type "${type}"`);
			return type;
	}
}

function generateArguments(methodArgs, testArgs) {
	const keys = Object.keys(testArgs);
	const values = keys.map((key) => {
		let value = testArgs[key];

		for (let i = 0; i < keys.length; i++) {
			if (methodArgs[i].name === key) {
				value = {
					name: key,
					type: getLanguageType(methodArgs[i].type),
					value: getValue(methodArgs[i], testArgs[key])
				};
			}
		}

		return value;
	});

	return values;
}

function generateArgumentString(methodArgs) {
	const names = methodArgs.map((arg) => {
		return arg.name;
	});

	return names.join(', ');
}

function readClass(uml) {
	const umlClass = {};

	umlClass.name = uml.name;
	umlClass.methods = uml.methods.map((m) => {
		const preconditions = {};
		m.preconditions.map((c) => {
			preconditions[c.id] = c;
		});

		const tests = smt[m.name].map((t) => {
			if (t.args === 'Unsatisfiable') {
				return null;
			}

			// TODO: Organise this better.
			// Redundant search through preconditions occurs in generateTestMethodName.
			// Could pass value directly via preconditions object.
			let testId;
			let exception = undefined;

			if (t.condition.indexOf(' ') >= 0) {
				testId = t.condition.split(' ')[1];
				// This will mean exception is either defined to the corresponding
				//  precondition's exception, or it will be undefined.'
			 	exception = preconditions[testId].exception;
			}
			else {
				// Else the condition is probably 'Valid'.
				testId = t.condition;
			}

			const test = {
				name: generateTestMethodName(m, testId),
				args: generateArguments(m.arguments, t.args),
				argumentString: generateArgumentString(m.arguments),
				exception: exception
			};

			return test;
		});

		const r = m.return;
		r.type = getLanguageType(r.type);

		const method = {
			name: m.name,
			arguments: m.arguments,
			return: r,
			preconditions: preconditions,
			postconditions: m.postconditions,
			tests: tests
		};

		return method;
	});

	console.log(JSON.stringify(umlClass, null, 2));

	return umlClass;
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

	initializing() {
		uml = require(path.resolve(process.cwd(), this.umlFile));
		smt = require(path.resolve(process.cwd(), this.smtFile));
	},

	configuring() {
		classes[0] = readClass(uml);
	},

	writing() {
		classes.map((c) => {
			this.template('test-class.cs', `build/${c.name}.cs`, { classObject: c });
		});
	}
});

module.exports = generator;

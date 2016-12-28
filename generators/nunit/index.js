const Generator = require('yeoman-generator');

const path = require('path');
const glob = require('glob');

const comparisons = require('../../util/comparisons.js');

function generateTestMethodName(method, testId) {
	let condition;
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

		clean = `Not${comparisons.toName(condition.comparison)}_${condition.arguments.join('_')}`;
	}

	return `test_${method.name}_${clean}`;
}


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
	const names = Object.keys(methodArgs).map((arg) => {
		return arg.name;
	});

	return names.join(', ');
}

function readClass(uml) {
	const umlClass = {};

	umlClass.name = uml.name;
	umlClass.methods = Object.keys(uml.methods).map((key) => {
		const m = uml.methods[key];

		// Handling tests
		const preconditions = {};

		m.preconditions.map((c) => {
			preconditions[c.id] = c;
		});

		const tests = m.tests.map((t) => {
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
				try {
					exception = preconditions[testId].exception;
				}
				catch (ex) {
					exception = undefined;
				}
			}
			else {
				// Else the condition is probably 'Valid'.
				testId = t.condition;
			}

			const test = {
				name: generateTestMethodName(m, testId),
				args: t.args,
				argumentString: generateArgumentString(m.arguments),
				exception: exception
			};

			return test;
		});

		// Return type handling
		const type = getLanguageType(m.type);

		const method = {
			name: m.name,
			arguments: m.arguments,
			type: type,
			preconditions: preconditions,
			postconditions: m.postconditions,
			tests: tests
		};

		return method;
	});

	console.log(JSON.stringify(umlClass, null, 2));

	return umlClass;
}

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

		console.log('NUnit');
	}

	initializing() {
		this.model = parseModel(this.options.model);
		this.composeWith(require.resolve('../helper'), {
			model: this.options.model
		});
	}

	configuring() {
		console.log('NUnit');
		console.log(this.model);
		this.classes = Object.keys(this.model).map((className) => {
			return readClass(this.model[className]);
		});
	}

	writing() {
		this.classes.map((c) => {
			this.template('test-class.cs', `build/${c.name}Test.cs`, { classObject: c });
		});
	}
};

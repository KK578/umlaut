const generators = require('yeoman-generator');

const path = require('path');
const glob = require('glob');

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
	const names = methodArgs.map((arg) => {
		return arg.name;
	});

	return names.join(', ');
}

function readClass(uml, smt) {
	const umlClass = {};

	umlClass.name = uml.name;
	umlClass.methods = Object.keys(uml.methods).map((key) => {
		const m = uml.methods[key];

		// Handling tests
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
				args: generateArguments(m.arguments, t.args),
				argumentString: generateArgumentString(m.arguments),
				exception: exception
			};

			return test;
		});

		// Return type handling
		const returnType = m.returnType;

		returnType.type = getLanguageType(returnType.type);

		const method = {
			name: m.name,
			arguments: m.arguments,
			return: returnType,
			preconditions: preconditions,
			postconditions: m.postconditions,
			tests: tests
		};

		return method;
	});

	// console.log(JSON.stringify(umlClass, null, 2));

	return umlClass;
}

const generator = generators.Base.extend({
	constructor: function () {
		generators.Base.apply(this, arguments);

		this.argument('umlFolder', {
			type: String,
			description: 'Directory path for JSON objects describing the model',
			required: true
		});
		this.argument('smtFolder', {
			type: String,
			description: 'Directory path for JSON objects describing the solved conditions',
			required: true
		});

		this.uml = {};
		this.smt = {};
	},

	initializing() {
		const done = this.async();
		const umlPath = path.resolve(process.cwd(), this.umlFolder);

		glob('*.json', { cwd: umlPath }, (err, files) => {
			if (err) {
				throw err;
			}

			let count = files.length;

			files.map((umlFile) => {
				const className = umlFile.substring(0, umlFile.length - 5);

				// UML/ClassName.json
				this.uml[className] = require(path.resolve(umlPath, umlFile));
				// SMT/ClassName/solved.json
				this.smt[className] = require(path.resolve(this.smtFolder, className, 'solved.json'));

				if (--count === 0) {
					done();
				}
			});
		});
	},

	configuring() {
		this.classes = Object.keys(this.uml).map((className) => {
			return readClass(this.uml[className], this.smt[className]);
		});
	},

	writing() {
		this.classes.map((c) => {
			this.template('test-class.cs', `build/${c.name}Test.cs`, { classObject: c });
		});
	}
});

module.exports = generator;

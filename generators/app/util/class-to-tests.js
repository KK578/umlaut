const comparisons = require('../../../util/comparisons.js');

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

function readTest(method, test) {
	const initialise = Object.keys(test.arguments).map((name) => {
		return {
			name: name,
			type: method.arguments[name],
			value: test.arguments[name]
		};
	});

	const run = [
		{
			name: 'result',
			type: method.type,
			value: {
				type: 'function-call',
				name: method.name,
				arguments: Object.keys(method.arguments)
			}
		}
	];

	const assertions = method.postconditions;

	return {
		initialise,
		run,
		assertions
	};
}

function readMethod(m) {
	// Handling tests
	const preconditions = {};

	m.preconditions.map((c) => {
		preconditions[c.id] = c;
	});

	// Return type handling
	const type = getLanguageType(m.type);

	const tests = m.tests.map((t) => {
		if (t.arguments === 'Unsatisfiable') {
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
			arguments: t.arguments,
			exception: exception
		};

		return test;
	});

	const postconditions = m.postconditions.map((c) => {
		c.comparison = comparisons.toSymbol(c.comparison);

		return c;
	});

	const method = {
		name: m.name,
		type: type,
		postconditions: postconditions,
		tests: tests
	};

	return method;
}

module.exports = (uml) => {
	const testClass = {};

	testClass.name = uml.name;
	testClass.methods = Object.keys(uml.methods).map((name) => {
		return readMethod(uml.methods[name]);
	});

	return testClass;
};

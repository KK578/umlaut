const Smt = require('../util/classes.js');
const comparisons = require('../../../util/comparisons.js');

function convertType(type) {
	switch (type) {
		case 'Integer':
			return 'Int';

		case 'Float':
		case 'Double':
			return 'Real';

		default:
			return type;
	}
}

function declareArguments(args) {
	const commands = [];
	const constants = {};

	// For every argument to the function, add a declaration to SMT.
	Object.keys(args).forEach((name) => {
		const type = convertType(args[name]);
		const command = new Smt.DeclareConst(name, type);

		// Note the existence of the argument to the class for get-value calls later.
		if (!constants[name]) {
			constants[name] = true;
		}

		commands.push(command);
	});

	return { commands, constants };
}

// Declare the function to SMT.
function declareFunction(method) {
	const commands = [];
	const type = convertType(method.type);
	const args = Object.keys(method.arguments).map((t) => {
		return convertType(method.arguments[t]);
	});
	const command = new Smt.DeclareFunction(method.name, type, args);

	commands.push(command);

	return commands;
}

function assertConditions(conditions) {
	const commands = [];

	conditions.forEach((condition) => {
		const comparison = comparisons.toSmtSymbol(condition.comparison);
		const command = new Smt.BooleanExpression(comparison,
			condition.arguments, condition.inverted);

		commands.push(new Smt.Assertion(command));
	});

	return commands;
}

function assertConditionsWithInverts(conditions, complementSet) {
	const commands = [];

	conditions.forEach((condition) => {
		const comparison = comparisons.toSmtSymbol(condition.comparison);
		const command = new Smt.BooleanExpression(comparison,
			condition.arguments, condition.inverted);

		complementSet.forEach((complement) => {
			if (condition === complement) {
				command.setInverted(!command.isInverted);
			}
		});

		commands.push(new Smt.Assertion(command));
	});

	return commands;
}

function addStackMessage(commands, message, constants) {
	const newCommands = [];

	// Start a new stack frame and echo a message for what conditions are occuring within it.
	newCommands.push(new Smt.Echo(message));
	newCommands.push(new Smt.StackModifier('push'));
	// Maintain the current set of commands.
	newCommands.push(...commands);
	// Check satisfiability and get values of arguments.
	newCommands.push(new Smt.GetValue(constants));
	newCommands.push(new Smt.StackModifier('pop'));

	return newCommands;
}

// Add a layer to the stack so we can pop later and keep the declarations.
function assertMethodConditions(method, constants) {
	let commands = [];

	// For each precondition, add it to the assertion stack.
	commands.push(...assertConditions(method.preconditions));

	// Declare a variable for the result.
	if (method.type !== 'void') {
		const resultType = convertType(method.type);
		const resultDeclare = new Smt.DeclareConst('result', resultType);

		const functionArgs = Object.keys(method.arguments);
		const functionCall = new Smt.FunctionCall(method.name, functionArgs);
		const resultAssert = new Smt.Assertion(
			new Smt.BooleanExpression('=', ['result', functionCall])
		);

		commands.push(resultDeclare);
		commands.push(resultAssert);
	}

	// For each postcondition, add it to the assertion stack to make inputs more informative.
	commands.push(...assertConditions(method.postconditions));

	// Wrap the above commands into the 'Valid' stack frame in z3.
	// This indicates to z3-runner that this set of commands will output the inputs which
	//  correspond to all preconditions being successfully fulfilled.
	commands = addStackMessage(commands, '[[Valid]]', constants);

	// Add assertions where a subset of conditions is inverted.
	const complementAssertionCommands = complementConditions(method.preconditions, constants);

	commands.push(...complementAssertionCommands);

	return commands;
}

/**
 * Adapted from solution for finding power set:
 * https://codereview.stackexchange.com/questions/7001/generating-all-combinations-of-an-array
 */
function getAllCombinations(list) {
	const result = [];

	function f(a, list) {
		list.forEach((c, i) => {
			const next = a.concat([c]);

			result.push(next);
			f(next, list.slice(i + 1));
		});
	}

	f([], list);

	return result;
}

function assertMethodOptionalConditions(method, constants) {
	if (!Array.isArray(method.optionalPreconditions) ||
		method.optionalPreconditions.length === 0) {
		return [];
	}

	const commands = [];

	// Add a layer to the stack to contain everything related to the optional conditions in its
	//  own frame.
	commands.push(new Smt.StackModifier('push'));

	// Optional preconditions are bound under the main preconditions, so they must also be
	//  fulfilled.
	commands.push(...assertConditions(method.preconditions));

	// Next assert all optional preconditions being fulfilled.
	// Wrap this set of commands into the 'ValidOptional' stack frame in z3.
	// This indicates to z3-runner that this set of commands will output the inputs which
	//  correspond to all *optional* preconditions being successfully fulfilled as well.
	const optionalConditionAssertionCommands = assertConditions(method.optionalPreconditions);
	const stackedCommands = addStackMessage(optionalConditionAssertionCommands, '~~[[ValidOptional]]', constants);

	commands.push(...stackedCommands);

	// Generate inputs when subsets of optional preconditions are complemented.
	commands.push(...complementConditions(method.optionalPreconditions, constants));

	// Remove stack layer for optional conditions.
	commands.push(new Smt.StackModifier('pop'));

	return commands;
}

function assertComplementedConditions(conditions, complementSets, constants) {
	const commands = [];

	complementSets.forEach((complementSet) => {
		const assertionCommands = assertConditionsWithInverts(conditions, complementSet);
		// Concatenate all IDs in the current complement set together.
		const complementedIds = complementSet.map((o) => {
			return o.id;
		}).join(',');
		const complementString = `~~[[${complementedIds}]]`;
		const stackedCommands = addStackMessage(assertionCommands, complementString, constants);

		commands.push(...stackedCommands);
	});

	return commands;
}

function complementConditions(conditions, constants) {
	const complementSets = getAllCombinations(conditions);
	const commands = assertComplementedConditions(conditions, complementSets, constants);

	return commands;
}

module.exports = class SmtMethod {
	constructor(method) {
		const declareArgCommands = declareArguments(method.arguments);
		const constants = Object.keys(declareArgCommands.constants);

		this.commands = declareArgCommands.commands.concat(
			declareFunction(method),
			assertMethodConditions(method, constants),
			assertMethodOptionalConditions(method, constants)
		);
	}

	getCommands() {
		return this.commands;
	}
};

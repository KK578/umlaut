const uuid = require('uuid/v4');
const promises = require('../../../util/promises.js');
const cfgParser = require('./condition-cfg-parser.js');

const classes = require('../../util/classes.js');
const AnnotatedUmlClass = classes.AnnotatedUmlClass;

function getTypeFromNode(parameter) {
	let type = '';

	if (parameter.type_NamedElement) {
		const namedElement = parameter.type_NamedElement[0];

		if (namedElement.primitiveTypeMoniker) {
			type = namedElement.primitiveTypeMoniker[0].$.LastKnownName;
		}
		else if (namedElement.undefinedTypeMoniker) {
			type = namedElement.undefinedTypeMoniker[0].$.LastKnownName;
		}
		else if (namedElement.referencedTypeMoniker) {
			type = namedElement.referencedTypeMoniker[0].$.LastKnownName;
		}
		else {
			throw new Error('Could not find type.');
		}
	}
	else {
		type = 'Object';
	}

	return type;
}

function parseVariables(umlClass) {
	const variables = [];

	// Iterate through list of attributes.
	if (umlClass.ownedAttributesInternal !== undefined) {
		const properties = umlClass.ownedAttributesInternal[0].property;

		properties.map((property) => {
			const v = {
				id: uuid(),
				name: property.$.name
			};

			v.visibility = property.$.visibility ? property.$.visibility : 'Public';
			v.type = getTypeFromNode(property);

			variables.push(v);
		});
	}

	return variables;
}

function parseMethods(umlClass) {
	const methods = [];

	// Helper function to get function return type.
	function getReturnType(parameters) {
		// Must iterate through all and find first that is a return property.
		const parameterList = parameters[0].operationHasOwnedParameters;

		for (let i = 0; i < parameterList.length; i++) {
			const parameter = parameterList[i].parameter[0];

			// Direction 'Return' indicates the function's return type.
			// TODO: Will the system support Python's multiple object return?'
			if (parameter.$.direction === 'Return') {
				const type = getTypeFromNode(parameter);

				return type;
			}
		}

		// Did not find a return type, so function has void type.
		return 'Void';
	}

	// Helper function to get function arguments to array of { name, type }.
	function getArguments(parameters) {
		const args = [];

		const parameterList = parameters[0].operationHasOwnedParameters;

		for (let i = 0; i < parameterList.length; i++) {
			const parameter = parameterList[i].parameter[0];

			// Direction 'In' indicates a function argument.
			if (parameter.$.direction === 'In') {
				args.push({
					name: parameter.$.name,
					type: getTypeFromNode(parameter)
				});
			}
		}

		return args;
	}

	// Helper function to take a condition from XML format to standardised format.
	function getConditions(conditions) {
		let c = [];

		function parseConditions(conditions) {
			const parsed = cfgParser(conditions);

			parsed.forEach((condition) => {
				condition.id = uuid();
			});

			return parsed;
		}

		if (conditions) {
			const constraint = conditions[0].constraint[0];
			const conditionString = constraint.specification[0].literalString[0].$.value;

			c = parseConditions(conditionString);
		}

		return c;
	}

	// Iterate through all methods.
	if (umlClass.ownedOperationsInternal !== undefined) {
		const operations = umlClass.ownedOperationsInternal[0].operation;

		operations.map((operation) => {
			// Generic method properties
			const v = {
				id: uuid(),
				name: operation.$.name
			};

			v.visibility = operation.$.visibility ? operation.$.visibility : 'Public';

			// Types
			v.type = getReturnType(operation.ownedParameters);
			v.arguments = getArguments(operation.ownedParameters);

			// Conditions
			v.preconditions = getConditions(operation.preconditionsInternal);
			v.postconditions = getConditions(operation.postconditionsInternal);

			// TODO: Keep method list as a hashmap of method name?
			methods.push(v);
		});
	}

	return methods;
}

function parseClass(umlClass) {
	const c = new AnnotatedUmlClass(umlClass.$.name);

	// Locate generic class properties.
	c.id = uuid();
	c.name = umlClass.$.name;

	// Parse information for class variables and methods.
	parseVariables(umlClass).forEach((variable) => {
		c.addVariable(variable);
	});
	parseMethods(umlClass).forEach((method) => {
		c.addMethod(method);

		method.preconditions.forEach((condition) => {
			c.methods[method.name].addPrecondition(condition);
		});

		method.postconditions.forEach((condition) => {
			c.methods[method.name].addPostcondition(condition);
		});
	});

	return c;
}

function parse(data) {
	return promises.xmlParseString(data).then((uml) => {
		// Enter root item.
		const classes = {};

		if (uml.modelStoreModel) {
			uml = uml.modelStoreModel;
		}
		else if (uml.logicalClassDesignerModel) {
			uml = uml.logicalClassDesignerModel;
		}

		const elements = uml.packagedElements[0];

		if (elements.packageHasNamedElement) {
			elements.packageHasNamedElement.map((namedElement) => {
				if (namedElement.class) {
					const c = parseClass(namedElement.class[0]);

					classes[c.name] = c;
				}
			});
		}

		if (elements.logicalClassDesignerModelHasTypes) {
			elements.logicalClassDesignerModelHasTypes.map((namedElement) => {
				if (namedElement.class) {
					const c = parseClass(namedElement.class[0]);

					classes[c.name] = c;
				}
			});
		}

		return classes;
	});
}

module.exports = parse;

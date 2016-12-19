const xml2js = require('xml2js');

function parseVariables(umlClass) {
	const variables = {};

	// Iterate through list of attributes.
	if (umlClass.ownedAttributesInternal !== undefined) {
		const properties = umlClass.ownedAttributesInternal[0].property;

		properties.map((property) => {
			const v = {
				id: property.$.Id,
				name: property.$.name
			};

			let type = '';

			// Get argument type defaulting to Object.
			if (property.type_NamedElement) {
				type = property.type_NamedElement[0];

				if (type.primitiveTypeMoniker) {
					type = type.primitiveTypeMoniker[0].$.LastKnownName;
				}
				else if (type.undefinedTypeMoniker) {
					type = type.undefinedTypeMoniker[0].$.LastKnownName;
				}
			}
			else {
				type = 'Object';
			}

			v.type = type;

			variables[v.name] = v;
		});
	}

	return variables;
}

function parseMethods(umlClass) {
	const methods = {};

	// Helper function to get function return type.
	function getReturnType(parameters) {
		// Must iterate through all and find first that is a return property.
		const parameterList = parameters[0].operationHasOwnedParameters;

		for (let i = 0; i < parameterList.length; i++) {
			const parameter = parameterList[i].parameter[0];

			// Direction 'Return' indicates the function's return type.
			// TODO: Will the system support Python's multiple object return?'
			if (parameter.$.direction === 'Return') {
				let type = '';

				if (parameter.$.name) {
					type = parameter.$.name;
				}
				else if (parameter.type_NamedElement) {
					type = parameter.type_NamedElement[0].primitiveTypeMoniker[0].$.LastKnownName;
				}

				return { type };
			}
		}

		// Did not find a return type, so function has void type.
		return { type: 'Void' };
	}

	// Helper function to get function arguments to array of { name, type }.
	function getArguments(parameters) {
		const args = [];

		const parameterList = parameters[0].operationHasOwnedParameters;

		for (let i = 0; i < parameterList.length; i++) {
			const parameter = parameterList[i].parameter[0];

			// Direction 'In' indicates a function argument.
			if (parameter.$.direction === 'In') {
				let name = '';
				let type = '';

				// Get argument name.
				if (parameter.$.name) {
					name = parameter.$.name;
				}

				// Get argument type defaulting to Object.
				if (parameter.type_NamedElement) {
					type = parameter.type_NamedElement[0].primitiveTypeMoniker[0].$.LastKnownName;
				}
				else {
					type = 'Object';
				}

				args.push({ name, type });
			}
		}

		return args;
	}

	// Helper function to take a condition from XML format to standardised format.
	// TODO: Replace inner workings with an AST parser.
	function getConditions(conditions) {
		let c = [];
		let id = '';

		function getConditionArguments(args) {
			const result = [];

			args.map((a) => {
				if (!a.startsWith('Exception')) {
					result.push(a);
				}
			});

			return result;
		}

		function getConditionException(args) {
			let result = undefined;

			args.map((a) => {
				if (a.startsWith('Exception')) {
					result = {
						type: a.split(':')[1]
					};
				}
			});

			return result;
		}

		function setupCondition(condition, index) {
			condition = condition.substring(1, condition.length - 1);

			const split = condition.split(' ');
			const args = getConditionArguments(split.slice(1));
			const exception = getConditionException(split.slice(1));

			return {
				id: `${id}-${index}`,
				comparison: split[0],
				arguments: args,
				exception: exception
			};
		}

		function parseConditions(conditions) {
			const split = conditions.split('-----');

			c = split.map(setupCondition);
		}

		if (conditions) {
			const constraint = conditions[0].constraint[0];
			const rawString = constraint.specification[0].literalString[0].$.value;

			id = constraint.$.Id;
			parseConditions(rawString);
		}

		return c;
	}

	// Iterate through all methods.
	if (umlClass.ownedOperationsInternal !== undefined) {
		const operations = umlClass.ownedOperationsInternal[0].operation;

		operations.map((operation) => {
			// Generic method properties
			const v = {
				id: operation.$.Id,
				name: operation.$.name
			};

			// Types
			v.returnType = getReturnType(operation.ownedParameters);
			v.arguments = getArguments(operation.ownedParameters);

			// Conditions
			v.preconditions = getConditions(operation.preconditionsInternal);
			v.postconditions = getConditions(operation.postconditionsInternal);

			// TODO: Keep method list as a hashmap of method name?
			methods[v.name] = v;
		});
	}

	return methods;
}

function parseClass(umlClass) {
	const c = {};

	// Locate generic class properties.
	c.id = umlClass.$.Id;
	c.name = umlClass.$.name;

	// Parse information for class variables and methods.
	c.variables = parseVariables(umlClass);
	c.methods = parseMethods(umlClass);

	return c;
}

function parse(data) {
	function promiseXmlParseString(xml) {
		const xmlParser = new xml2js.Parser();

		return new Promise((resolve, reject) => {
			xmlParser.parseString(xml, (err, data) => {
				if (err) {
					reject(err);
				}
				else {
					resolve(data);
				}
			});
		});
	}

	return promiseXmlParseString(data).then((uml) => {
		// Enter root item.
		const classes = {};

		uml = uml.modelStoreModel;

		uml.packagedElements.map((element) => {
			// All related items are stored as namedElement objects in the package's elements.
			// Iterate through all and for objects representing classes, parse them.
			element.packageHasNamedElement.map((namedElement) => {
				if (namedElement.class) {
					const c = parseClass(namedElement.class[0]);

					classes[c.name] = c;
				}
			});
		});

		return classes;
	})
}

module.exports = parse;

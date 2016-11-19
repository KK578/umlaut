function parseVariables(umlClass) {
	const variables = {};

	// Iterate through list of attributes.
	umlClass.ownedAttributesInternal[0].property.map((property) => {
		const v = {
			id: property.$.Id,
			name: property.$.name,
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

	return variables;
}

function parseMethods(umlClass) {
	const methods = {};

	// Helper function to get function return type.
	function getReturnType(parameters) {
		// Must iterate through all and find first that is a return property.
		for (let i = 0; i < parameters.length; i++) {
			const parameter = parameters[i].operationHasOwnedParameters[0].parameter[0];

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

		for (let i = 0; i < parameters.length; i++) {
			const parameter = parameters[i].operationHasOwnedParameters[0].parameter[0];

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
	function getConditions(conditions) {
		const c = {};

		if (conditions) {
			const constraint = conditions[0].constraint[0];
			const rawString = constraint.specification[0].literalString[0].$.value;

			c.id = constraint.$.Id;
			// TODO: Add a character to split off of while using Visual Studio's inbuilt
			//  property conditions.
			// TODO: Parse condition string into object splitting into comparison and arguments.
			// NOTE: Leave parsing until after Visual Studio plugin is designed, may use a
			//  simpler system.
			c.string = rawString;
		}

		return c;
	}

	// Iterate through all methods.
	umlClass.ownedOperationsInternal[0].operation.map((operation) => {
		// Generic method properties
		const v = {
			id: operation.$.Id,
			name: operation.$.name,
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

function parse(uml) {
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

	console.log(JSON.stringify(classes, null, 2));

	return classes;
}

module.exports = parse;

const SmtMethod = require('./method.js');

module.exports = class SmtClass {
	constructor(classObject) {
		this.name = classObject.name;
		this.smtCommands = Object.keys(classObject.methods).map((m) => {
			const method = classObject.methods[m];
			const smtMethod = new SmtMethod(method);
			const commands = smtMethod.getCommands().map((command) => {
				return command.toString();
			});

			return {
				name: method.name,
				commands: commands
			};
		});
	}
};

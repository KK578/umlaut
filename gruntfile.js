function initTimeGrunt(grunt) {
	const timeGrunt = require('time-grunt');

	timeGrunt(grunt);
}

function initLoadGruntConfig(grunt) {
	const loadGruntConfig = require('load-grunt-config');
	const options = {
		jitGrunt: {
			staticMappings: {
				bower: 'grunt-bower-task',
				express: 'grunt-express-server',
				minifyPolymerCSS: 'grunt-minify-polymer',
				mochaTest: 'grunt-mocha-test',
				sasslint: 'grunt-sass-lint'
			}
		}
	};

	loadGruntConfig(grunt, options);
}

function quietGruntNewer(grunt) {
	const originalHeader = grunt.log.header;
	const originalWriteLn = grunt.log.writeln;

	// Cannot use arrow functions here as the this object is incorrect otherwise.
	grunt.log.header = function (message) {
		// Only if the header does not start with newer or newer-postrun.
		if (!/newer(-postrun)?:/.test(message)) {
			originalHeader.apply(this, arguments);
		}

		return this;
	};

	// Cannot use arrow functions here as the this object is incorrect otherwise.
	grunt.log.writeln = function (message) {
		// Only write the message if it is not the text from a grunt-newer task.
		if (message !== 'No newer files to process.') {
			originalWriteLn.apply(this, arguments);
		}

		// Need to return the object as in grunt-legacy-log#writeln.
		return this;
	};
}

module.exports = function (grunt) {
	initTimeGrunt(grunt);
	initLoadGruntConfig(grunt);
	quietGruntNewer(grunt);
};

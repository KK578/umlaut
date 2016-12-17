const glob = require('glob');
const path = require('path');

const testSuite = {};

function submoduleTests(submodule, done) {
	const subPath = path.join(__dirname, submodule);
	const tests = [];

	console.log('Why');

	glob('*-test.js', { cwd: subPath }, (err, files) => {
		if (err) {
			done(err);
		}

		files.map((test) => {
			tests.push(path.join(subPath, test));
		});
		console.log(tests);

		done(tests);
	});
}

before('uml-parser', function (done) {
	submoduleTests('uml-parser', (tests) => {
		testSuite['uml-parser'] = tests;
		done();
	});
});

describe('pls', () => {
	it('gib');

	for (const suite in testSuite) {
		console.log(suite);
		describe(suite, () => {
			it('kek');
			require(testSuite[suite]);
		});
	}
});

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	public class OclCondition
	{
		public string Comparator { get; set; }
		private List<string> arguments;

		public OclCondition()
		{
			arguments = new List<string>();
		}

		public void SetArguments(string argument)
		{
			arguments = new List<string>(argument.Split('\n'));
		}

		public override string ToString()
		{
			return String.Format("({0} {1})", Comparator, String.Join(" ", arguments));
		}
	}
}

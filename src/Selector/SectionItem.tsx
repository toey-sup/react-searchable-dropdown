import React, {
  memo, useRef, useState, useEffect,
} from 'react';
import Tooltip from '@material-ui/core/Tooltip';
import { makeStyles } from '@material-ui/core/styles';
import Typography from '@material-ui/core/Typography';

const useStyles = makeStyles({
  sectionName: {
    backgroundColor: '#F7F7F7',
    borderTop: '1px solid #F3F3F3',
    borderBottom: '1px solid #F3F3F3',
    padding: '8px 16px',
  },
  choice: {
    cursor: 'pointer',
    position: 'relative',
    alignItems: 'center',
    display: 'flex',
    height: '100%',
    padding: '0px 16px',
    '&:hover': {
      backgroundColor: '#F8F8F8',
      '& $label': {
        color: '#828282',
      },
    },
  },
  usedChoice: {
    cursor: 'default',
    '& p': {
      color: '#F3F3F3',
    },
    '&:hover': {
      backgroundColor: 'white !important',
      '& $label': {
        color: '#F3F3F3',
      },
    },
  },
  checkbox: {
    padding: 0,
    marginRight: '10px',
  },
  line: (props: { lineWidth: number }) => ({
    width: props.lineWidth,
    color: '#F3F3F3',
    borderColor: '#F3F3F3',
    backgroundColor: '#F3F3F3',
    borderBlockStartStyle: 'none',
    borderBlockStartColor: '#F3F3F3',
    position: 'absolute',
  }),
  prefix: {
    color: '#63B178',
    whiteSpace: 'break-spaces',
    fontStyle: 'italic',
    userSelect: 'none',
    marginRight: '10px',
  },
  label: {
    userSelect: 'none',
    whiteSpace: 'nowrap',
    textOverflow: 'ellipsis',
    overflow: 'hidden',
  },
  tooltip: {
    zIndex: 12,
  },
});

export interface Choice {
  label: string;
  used?: boolean;
  description?: string;
  [key: string]: any;
}

export interface ChoiceSections {
  choices: Choice[];
  sectionName?: string;
  sectionPrefix?: any;
}

export interface Props {
  choice: Choice;
  id?:string;
  handleSelect: (choice: Choice) => void;
}

const SelectorItem: React.FC<Props> = memo(({
  choice,
  id,
  handleSelect,
}) => {
  const [lineWidth, setLineWidth] = useState<number>(0);
  const labelRef = useRef<HTMLParagraphElement>(null);
  const classes = useStyles({ lineWidth });

  useEffect(() => {
    if (labelRef.current) setLineWidth(labelRef.current.clientWidth + 20);
  }, []);

  return (
    <Tooltip
      title={<Typography style={{ whiteSpace: 'pre-line' }}>{`${choice?.sectionPrefix || ''} ${choice?.label}\n ${choice?.description ?? ''}`}</Typography>}
      key={`${choice?.sectionPrefix || ''} ${choice?.label}`}
      enterDelay={300}
      leaveDelay={0}
      enterNextDelay={200}
      interactive
      placement="right-start"
      arrow
      className={classes.tooltip}
    >
      <div
        key={choice?.fieldName || choice?.label}
        className={`${classes.choice}  ${(choice?.used) ? classes.usedChoice : ''}`}
        onClick={() => {
          if (!choice?.used) handleSelect(choice);
        }}
        id={`${id}-${choice?.label}`}
        aria-hidden="true"
      >
        {choice?.used && <hr className={classes.line} />}
        {choice?.sectionPrefix && (
        <Typography className={classes.prefix}>
          {choice?.sectionPrefix}
        </Typography>
        )}
        <Typography className={classes.label} ref={labelRef}>
          {choice?.label}
        </Typography>
      </div>
    </Tooltip>
  );
});

export default SelectorItem;
